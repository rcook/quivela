-- Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0
{-# LANGUAGE QuasiQuotes #-}

import Quivela
import qualified System.Exit as E

program =
  prove'
    emptyVerifyEnv
    [prog'|
function skenc(k, a, m)
function skdec(k, a, c)


method Enc(e) { new (const e=e,d=0) {
   method enc(a,m)      { c = e.enc(a,Z(m)) & d[a][c] = <m> & c } // do we need to add the !d[a][c] check?
   method dec(a,c)      { d[a][c] }
}}

// FIXME: We should unify these "strongly typed" constructors and the existing ones
type ET = new (const k) {
   method enc(a,m)      { skenc(k,a,m) }
   method dec(a,c)      { skdec(k,a,c) }
}
type EncT = new (const e: ET, d=0) {
   method enc(a,m)      { c = e.enc(a,Z(m)) & d[a][c] = <m> & c } // do we need to add the !d[a][c] check?
   method dec(a,c)      { d[a][c] }
}

method E() { new (const k=rnd()) {
   method enc(a,m)      { skenc(k,a,m) }
   method dec(a,c)      { skdec(k,a,c) }
}}

assume Enc(E()) ≈ E()

// primitive envelope encryption
method Env(e) { new (const e=e) {
    method enc(a,m)      { k = rnd() & ek = e.enc(0,k) & em = skenc(k,a,m) & <ek,em> }
    method dec(a,c)      { <ek,em> = c & k = e.dec(0,ek) & skdec(k,a,em) }
}}
// th: Enc(Env(Enc(e))) ~ Env(Enc(e)) {


method EncL(e) { new (const e=e,d=0) {
    method enc(a,m)      { c = e.enc(a,Z(m)) & d[a][c] = <m> & c }
}}

method EncLI(e) { new (const e=e) {
    method enc(a,m)      { e.enc(a,Z(m)) }
}}
e = adversary()
|] $
  [prog|
         Enc(Env(Enc(e))) |] ≈
  Hint [Note "defs"] :
  [prog|
new (const e = Env(Enc(e)),d=0) {
  method enc(a,m)      { c = e.enc(a,Z(m)) & d[a][c] = <m> & c }
  method dec(a,c)      { d[a][c] }
}|] ≈
  Hint [Note "defs, renaming e"] :
  [prog|
new (const e = Enc(e),d=0) {
  method enc(a,m)      { k=rnd() & ek = e.enc(0,k) & em = skenc(k,a,Z(m)) & c = <ek,em> & d[a][c] = <m> & c }
  method dec(a,c)      { d[a][c] }
}|] ≈
  Hint [Note "switching from Enc to EncL since no calls to dec"] :
  [prog|
new (const e = EncL(e),d=0) {
  method enc(a,m)      { k=rnd() & ek = e.enc(0,k) & em = skenc(k,a,Z(m)) & c = <ek,em> & d[a][c] = <m> & c }
  method dec(a,c)      { d[a][c] }
}|] ≈
  Hint [Note "assumption", rewrite "EncL(e)" "EncLI(e)"] :
  [prog|
new (const e = EncLI(e),d=0) {
  method enc(a,m)      { k=rnd() & ek = e.enc(0,k) & em = skenc(k,a,Z(m)) & c = <ek,em> & d[a][c] = <m> & c }
  method dec(a,c)      { d[a][c] }
}|] ≈
  Hint [Note "def e.enc; Z(k) ~ zk"] :
  [prog|
new (const e = EncLI(e),d=0) {
  method enc(a,m)      { k=rnd(), zk = Z(k) & ek = e.enc(0,zk) & em = skenc(k,a,Z(m)) & c = <ek,em> & d[a][c] = <m> & c }
// orig: enc(a,m)      { k=rnd() & ek = e.enc(0,zk) & em = skEnc(k,a,Z(m)) & c = <ek,em> & d[a][c] = <m> & c }
  method dec(a,c)      { d[a][c] }
}|] ≈
  Hint [Note "introducing f; def E"] :
  [prog|
new (const e = EncLI(e),d=0) {
  method enc(a,m)      { zk = Z(rnd()), f = E() & ek = e.enc(0,zk) & em = f.enc(a,Z(m)) & c = <ek,em> & d[a][c] = <m> & c }
// orig: enc(a,m)      { f = E() & ek = e.enc(0,zk) & em = f.enc(a,Z(m)) & c = <ek,em> & d[a][c] = <m> & c }
  method dec(a,c)      { d[a][c] }
}|] ≈
  Hint [rewrite "E()" "Enc(E())"] :
  [prog|
new (const e = EncLI(e),d=0) {
  method enc(a,m)      { zk = Z(rnd()), f = Enc(E()) & ek = e.enc(0,zk) & em = f.enc(a,Z(m)) & c = <ek,em> & d[a][c] = <m> & c }
  method dec(a,c)      { d[a][c] }
}|] ≈
  Hint
    [ Note
        "similar to above (f.dec not called) - replace Enc(E()) w EncLI(E()), then Z(m) w. m, then EncLI(E()) w. Enc(E())"
    ] :
  [prog|
new (const e = EncLI(e),d=0) {
  method enc(a,m)      { zk = Z(rnd()), f = Enc(E()) & ek = e.enc(0,zk) & em = f.enc(a,m) & c = <ek,em> & d[a][c] = <m> & c }
  method dec(a,c)      { d[a][c] }
}|] ≈
  Hint [Note "introduce fs, move to EncE()"] :
  [prog|
new (const e = EncLI(e),d=0, fs: map * EncT = 0) {
  method enc(a,m)      { zk = Z(rnd()), f = new EncT(e= new ET(k=rnd())) & ek = e.enc(0,zk) & em = f.enc(a,m) & fs[ek]=f & c = <ek,em> & d[a][c] = <m> & c }
  method dec(a,c: <*, *>) { d[a][c] } // todo: get rid of type annotation
  invariant i1(a,c)    { !d[a][c] | <ek,em> = d[a][c] & 1 }
  invariant i2(a,ek,em){ d[a][<ek,em>] == fs[ek].d[a][em] }
}|] ≈
  Hint [Note "address bijection doesn't remap result values"] :
  [prog|
   method dec(a,c)      { <ek,em> = c & fs[ek].dec(a, em) } |] ≈
  Hint [Note "d auxiliary"] :
  [prog|
new (...,delete d) {...
  delete i1
  delete i2
  method enc(a,m)      { zk = Z(rnd()), f = new EncT(e=new ET(k=rnd())) & ek = e.enc(0,zk) & em = f.enc(a,m) & fs[ek]=f & c = <ek,em> & c }
}|] ≈
  Hint [Note "tbd: unify EncT and Enc", Admit] :
  [prog|
new (const e = EncLI(e),fs:map * ET=0) {
    method enc(a,m)    { zk = Z(rnd()), f = new ET(k=rnd()) & ek = e.enc(0,zk) & em = f.enc(a,m) & fs[ek]=f & <ek,em> }
    method dec(a,c)    { <ek,em> = c & fs[ek].dec(a,em) }
}|] ≈
  Hint [Note "move from zk to f.k", NoAddressBijection] :
  [prog|
new (const e = EncLI(e),fs:map * ET=0) {
    method enc(a,m)    { zk = Z(rnd()), f = new ET(k=rnd()) & ek = e.enc(0,f.k) & em = f.enc(a,m) & fs[ek]=f & <ek,em> }
    method dec(a,c)    { <ek,em> = c & fs[ek].dec(a,em) }
}|] ≈
  Hint [Note "Drop zk"] :
  [prog|
new (const e = EncLI(e),fs:map * ET=0) {
    method enc(a,m)    { f = new ET(k=rnd()) & ek = e.enc(0,f.k) & em = f.enc(a,m) & fs[ek]=f & <ek,em> }
    method dec(a,c)    { <ek,em> = c & fs[ek].dec(a,em) }
}|] ≈
  Hint [] :
  [prog|
new (const e = EncL(e),fs:map * ET=0) {
    method enc(a,m)    { f = new ET(k=rnd()) & ek = e.enc(0,f.k) & em = f.enc(a,m) & fs[ek]=f & <ek,em> }
    method dec(a,c)    { <ek,em> = c & fs[ek].dec(a,em) }
}|] ≈
  Hint [Note "Move from fs[..].dec to using e and skdec"] :
  [prog|
new (const e = Enc(e),fs:map * ET=0) {
   method enc(a,m)    { f = new ET(k=rnd()) & ek = e.enc(0,f.k) & em = f.enc(a,m) & fs[ek]=f & <ek,em> }
   method dec(a,c)    { <ek,em> = c & k = e.dec(0,ek) & skdec(k,a,em) }
   invariant i1(ek)   { !fs[ek]  | fs[ek].k == e.d[0][ek] } // type of fs
   invariant i2(ek)   { !(fs[ek] == 0) | !e.d[0][ek] }
   invariant i3(ek)   { !(e.d[0][ek] == 0) | !fs[ek] }
}|] ≈
  Hint [Note "fs auxiliary"] :
  [prog|
new (const e = Enc(e)) {
   method enc(a,m)         { f = new ET(k=rnd()) & ek = e.enc(0,f.k) & em = f.enc(a,m) & <ek,em> }
   method dec(a,c)         { <ek,em> = c & k = e.dec(0,ek) & skdec(k,a,em) }
}|] ≈
  Hint [Note "inlining"] :
  [prog|
new (const e = Enc(e)) {
   method enc(a,m)         { k=rnd() & ek = e.enc(0,k) & em = skenc(k, a, m) & <ek,em> }
   method dec(a,c)         { <ek,em> = c & k = e.dec(0,ek) & skdec(k,a,em) }
}|] ≈
  Hint [Note "fold definitions"] :
  [prog|
Env(Enc(e)) |] :
  []

main :: IO ()
main = do
  n <- program
  if n == 0 then E.exitSuccess else E.exitFailure
