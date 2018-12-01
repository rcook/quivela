-- Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0
{-# LANGUAGE QuasiQuotes, TemplateHaskell #-}

module Quivela.Examples.FIFO
  ( program
  ) where

import Control.Lens
import Quivela

program =
  prove'
    emptyVerifyEnv
    [prog'|
   method Fifo(n) {
     new (const n=n, s:int=0, r:int=0, h=0) {
       method snd(m) { n.snd(Z(m)) & h[s] = <m>, s++, 1 }
       method rcv() { n.rcv() & r < s & h[r++] }
     }
   }
   method AEAD(e) {
     new (const e=e, d=0) {
       method enc(a, m) { c = e.enc(a, Z(m)) & d[a][c] = <m> & c }
       method dec(a, c) { d[a][c] }
     }
   }

   method ChC(n, e) { new(const n=n, const e=e, s:int=0, r:int=0) {
     method snd(m) { c = e.enc(s, m) & n.snd(c), s++, 1 }
     method rcv()  { c = n.rcv() & m = e.dec(r, c) & r++ , m }
   }}

   n = adversary(),
   e = adversary()
|] $
  let directEqs = map (fieldEqual . (: [])) ["s", "r", "h"]
      channelFields = [["n", "s"], ["n", "r"], ["n", "e", "d"]]
      eqs = directEqs ++ map (fieldEqual) channelFields
   in [prog|
   Fifo(ChC(n, AEAD(e)))|] ≈
      [prog|
new (const n=ChC(n,AEAD(e)),s:int=0,r:int=0, h=0) {
    method snd(m)    { n.snd(Z(m)) & h[s] = <m> , s++, 1 }
    method rcv()     { n.rcv() & r < s & h[r++] }
}|] ≈
      Hint ([Note "Unfold Fifo"]) :
      [prog|
new (const n=ChC(n,AEAD(e)),s:int=0,r:int=0, h=0) {
    method snd(m)    { (c = n.e.enc(n.s, Z(m)) & n.n.snd(c) , n.s++), c & h[s] = <m>, s++, 1 }
    method rcv()     { n.rcv() & r < s & h[r++] }
    invariant iR()   { n.r == r }
    invariant iS()   { n.s == s }
    invariant le()   { r <= s }
    invariant iED(a, c) { !n.e.d[a][c] | a < n.s }
}|] ≈
      Hint [Note "Move to ch.r and ch.s"] :
      [prog|
new (const n=ChC(n,AEAD(e)), h=0) {
    method snd(m)    { (c = n.e.enc(n.s, Z(m)) & n.n.snd(c) , n.s++), c & h[n.s-1] = <m>, 1 }
    method rcv()     { n.rcv() & h[n.r-1] }
    invariant le()   { n.r <= n.s }
    invariant iED(a, c) { !n.e.d[a][c] | a < n.s }
    invariant iH2(a, c) { !h[a] | a < n.s }
}|] ≈
      [prog|
    method snd(m)    { c = n.e.e.enc(n.s, Z(m)) & n.e.d[n.s][c] = <Z(m)> & n.n.snd(c) , n.s++, h[n.s-1] = <m>, 1 }
   |] ≈
      Hint [Note "introduce elts"] :
      [prog|
// Since we want to change the contents of n.e.d in this step, but retain which elements
// are non-zero, we introduce elts as a helper map that records this information and can
// be used by an equality hint to connect n.e.d on both sides
new (const n=ChC(n,AEAD(e)), h=0, elts=0) {
    method snd(m)    { c = n.e.e.enc(n.s, Z(m)) & elts[n.s][c] = 1 & n.e.d[n.s][c] = <Z(m)> & n.n.snd(c) , n.s++, h[n.s-1] = <m>, 1 }
    method rcv()     { n.rcv() & h[n.r-1] }
    invariant le()   { n.r <= n.s }
    invariant iED(a, c) { !n.e.d[a][c] | a < n.s }
    invariant iH2(a, c) { !h[a] | a < n.s }
    invariant iElts(a, c) { !elts[a][c] == !n.e.d[a][c] }
}|] ≈
      Hint
        ([Note "drop Z", NoInfer] ++
         map fieldEqual [["h"], ["elts"], ["n", "r"], ["n", "s"]]) :
      [prog|
new (const n=ChC(n,AEAD(e)), h=0, elts=0) {
    method snd(m)    { c = n.e.e.enc(n.s, Z(m)) & elts[n.s][c] = 1 & n.e.d[n.s][c] = <m> & n.n.snd(c) , n.s++, h[n.s-1] = <m>, 1 }
    method rcv()     { n.rcv() & h[n.r-1] }
    invariant le()   { n.r <= n.s }
    invariant iED(a, c) { !n.e.d[a][c] | a < n.s }
    invariant iH2(a, c) { !h[a] | a < n.s }
    invariant iElts(a, c) { !elts[a][c] == !n.e.d[a][c] }
}|] ≈
      Hint [Note "Drop elts"] :
      [prog|
new (const n=ChC(n,AEAD(e)), h=0) {
    method snd(m)    { c = n.e.e.enc(n.s, Z(m)) & n.e.d[n.s][c] = <m> & n.n.snd(c) , n.s++, h[n.s-1] = <m>, 1 }
    method rcv()     { n.rcv() & h[n.r-1] }
    invariant le()   { n.r <= n.s }
    invariant iED(a, c) { !n.e.d[a][c] | a < n.s }
    invariant iH2(a, c) { !h[a] | a < n.s }
}|] ≈
      Hint [Admit] :
      [prog|
    method snd(m)    { c = n.e.e.enc(n.s, Z(m)) & n.e.d[n.s][c] = <m>, n.n.snd(c) , n.s++, h[n.s-1] = <m>, 1 }
    method rcv()     { n.rcv() & h[n.r-1] }
   |] ≈
      Hint [] :
      [prog|
    invariant iH(a, c) { !n.e.d[a][c] | h[a] == n.e.d[a][c] }
   |] ≈
      [prog|
    method rcv()     { (c = n.n.rcv() & m = n.e.dec(n.r, c) & n.r++, m) & h[n.r-1] }
   |] ≈
      [prog|
    method rcv()     { (c = n.n.rcv() & m = n.e.dec(n.r, c) & n.r++, m) }
   |] ≈
      [prog|
new (const n=ChC(n,AEAD(e))) {
    method snd(m)    { c = n.e.e.enc(n.s, Z(m)) & n.e.d[n.s][c] = <m>, n.n.snd(c) , n.s++, 1 }
    method rcv()     { (c = n.n.rcv() & m = n.e.dec(n.r, c) & n.r++, m) }
    invariant le()   { n.r <= n.s }
    invariant iED(a, c) { !n.e.d[a][c] | a < n.s }
}|] ≈
      [prog|
new (const n=ChC(n,AEAD(e))) {
    method snd(m)    { n.snd(m) }
    method rcv()     { n.rcv() }
}|] ≈
      Hint
        (zipWith
           fieldsEqual
           [["n", "r"], ["n", "s"], ["n", "e", "d"]]
           [["r"], ["s"], ["e", "d"]]) :
      [prog| ChC(n, AEAD(e)) |] : []
