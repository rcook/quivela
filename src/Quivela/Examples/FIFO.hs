{-# LANGUAGE TemplateHaskell, QuasiQuotes #-}
module Quivela.Examples.FIFO where
import Control.Lens
import Quivela

prove (set useCache False emptyVerifyEnv)
  [prog'|
   method Fifo(n) {
     new (const n=n, s:int=0, r:int=0, h=0) {
       method snd(m) { h[s++] = <m>, n.snd(Z(m)), 1 }
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
     method snd(m) { (c = e.enc(s, m) & n.snd(c) & s++), 1 }
     method rcv() { c = n.rcv() & m = e.dec(r, c) & r++ , m }
   }}

   n = adversary(),
   e = adversary()
|] $ let directEqs = map (fieldEqual . (:[])) ["s", "r", "h"]
         channelFields = [ ["n", "s"], ["n", "r"]
                          , ["n", "e", "d"] ]
         eqs = directEqs ++
               map (fieldEqual) channelFields in
   [prog| Fifo(ChC(n, AEAD(e))) |]
   ≈ Hint ([Note "Unfold Fifo", NoInfer] ++ eqs) :
   [prog|
new (const n=ChC(n,AEAD(e)),s=0,r=0,h=0) {
    method snd(m)    { h[s++] = <m>, n.snd(Z(m)), 1 }
    method rcv()     { n.rcv() & r<s & h[r++] }
}|]
   ≈ Hint ([Note "Rename n", NoInfer] ++ directEqs ++
           map (\chanField -> fieldsEqual chanField ("ch" : tail chanField)) channelFields): -- renaming n to ch, caching ch.n as n, ch.e.e as e
   [prog|
new (const n=n,const e=e,const ch=ChC(n,AEAD(e)),s=0,r=0,h=0) {
    method snd(m)    { h[s++] = <m>, ch.snd(Z(m)), 1 }
    method rcv()     { ch.rcv() & r<s & h[r++] }

}|]
   ≈ Hint [Note "Inline calls to ch.*"]:
   [prog|
new (const n=n, const e=e,const ch=ChC(n,AEAD(e)),s=0,r=0,h=0) {
    method snd(m)    { h[s++] = <m>, (c = ch.e.enc(ch.s,Z(m)) & n.snd(c) & ch.s++, 1), 1 }
    method rcv()     { (c = n.rcv() & m=ch.e.d[ch.r][c] & ch.r++, m) & r<s & h[r++] }

}|]
   ≈ Hint [Note "Inline call to ch.e.enc"]:
   [prog|
new (const n=n,const e=e,const ch=ChC(n,AEAD(e)),s=0,r=0,h=0) {
    method snd(m)    { h[s++] = <m>, ((c = e.enc(ch.s,Z(m)) & ch.e.d[ch.s][c] = <Z(m)> & c) & n.snd(c) & ch.s++, 1), 1 }
    method rcv()     { c = n.rcv() & m=ch.e.d[ch.r][c] & ch.r++, r<s & h[r++] }
}|]
   ≈ Hint [Note "Associativity; logic"]:
   [prog|
new (const n=n,const e=e,const ch=ChC(n,AEAD(e)),s=0,r=0,h=0) {
    method snd(m)    { h[s++] = <m>, (c = e.enc(ch.s,Z(m)) & ch.e.d[ch.s][c] = <Z(m)> & n.snd(c) & ch.s++), 1 }
    method rcv()     { c = n.rcv() & m=ch.e.d[ch.r][c] & ch.r++, r<s & h[r++] }
}|]
    ≈ Hint [Note "Adding invariants ch.s == s, ch.r == r"]:
   [prog|
new (const n=n,const e=e,const ch=ChC(n,AEAD(e)),s=0,r=0,h=0) {
    method snd(m)    { (c = e.enc(ch.s,Z(m)) & n.snd(c) & h[s++] = <m> & ch.e.d[ch.s][c] = <Z(m)> & ch.s++), 1 }
    method rcv()     { c = n.rcv() & m=ch.e.d[ch.r][c] & r<s & ch.r++, r<s & h[r++] }
    invariant iS()     { ch.s == s }
    invariant iR()     { ch.r == r }
}|]
    ≈ Hint [Note "Replace s and r by ch.s and ch.r"]:
    [prog|
new (const n=n,const e=e,const ch=ChC(n,AEAD(e)),s=0,r=0,h=0) {
    method snd(m)    { (c = e.enc(ch.s,Z(m)) & n.snd(c) & h[ch.s] = <m> & ch.e.d[ch.s][c] = <Z(m)> & ch.s++), 1 }
    method rcv()     { c = n.rcv() & m=ch.e.d[ch.r][c] & ch.r<ch.s & ch.r++, (ch.r-1)<ch.s & h[ch.r-1] }
}|]
    ≈ Hint [Note "Invariants ch.r <= ch.s and ch.e.d[a][c] ==> a < ch.s"]:
    [prog|
new (const n=n,const e=e,const ch=ChC(n,AEAD(e)),h=0) {
    method snd(m)    { (c = e.enc(ch.s,Z(m)) & n.snd(c) & h[ch.s] = <m> & ch.e.d[ch.s][c] = <Z(m)> & ch.s++), 1 }
    method rcv()     { c = n.rcv() & m=ch.e.d[ch.r][c] & ch.r<ch.s & ch.r++, (ch.r-1)<ch.s & h[ch.r-1] }
    invariant i1() { ch.r <= ch.s }
    invariant i2(a, c) { !ch.e.d[a][c] | a < ch.s }
}|]
    ≈ Hint [Note "Store m instead Z(m) in h"]:
    [prog|
new (const n=n,const e=e,const ch=ChC(n,AEAD(e)),h=0) {
    method snd(m)    { (c = e.enc(ch.s,Z(m)) & n.snd(c) & h[ch.s] = <m> & ch.e.d[ch.s][c] = <Z(m)> & ch.s++), 1 }
    method rcv()     { c = n.rcv() & m=ch.e.d[ch.r][c] & ch.r++, h[ch.r-1] }
    invariant i1() { ch.r <= ch.s }
    invariant i2(a, c) { !ch.e.d[a][c] | a < ch.s }
}|]
    ≈ Hint [Note "Invariant ch.e.d[a][c] ==> h[a] == ch.e.d[a][c]"]:
    [prog|
new (const n=n,const e=e,const ch=ChC(n,AEAD(e)),h=0) {
    method snd(m)    { (c = e.enc(ch.s,Z(m)) & n.snd(c) & h[ch.s] = <m> & ch.e.d[ch.s][c] = <m> & ch.s++), 1 }
    method rcv()     { c = n.rcv() & m=ch.e.d[ch.r][c] & ch.r++, h[ch.r-1] }
    invariant i1() { ch.r <= ch.s }
    invariant i2(a, c) { !ch.e.d[a][c] | a < ch.s }
    invariant i3(a, c) { !ch.e.d[a][c] | h[a] == ch.e.d[a][c] }
}|]
    ≈ Hint [Note "Replace h[ch.r-1] by m"]:
    [prog|
new (const n=n,const e=e,const ch=ChC(n,AEAD(e)),h=0) {
    method snd(m)    { (c = e.enc(ch.s,Z(m)) & n.snd(c) & h[ch.s] = <m> & ch.e.d[ch.s][c] = <m> & ch.s++), 1 }
    method rcv()     { c = n.rcv() & m=ch.e.d[ch.r][c] & ch.r++, m }
    invariant i1() { ch.r <= ch.s }
    invariant i2(a, c) { !ch.e.d[a][c] | a < ch.s }
    invariant i3(a, c) { !ch.e.d[a][c] | h[a] == ch.e.d[a][c] }
}|]
    ≈ Hint [Note "h auxiliary"]:
    [prog|
new (const n=n,const e=e,const ch=ChC(n,AEAD(e))) {
    method snd(m)    { (c = e.enc(ch.s,Z(m)) & n.snd(c) & ch.e.d[ch.s][c] = <m> & ch.s++), 1 }
    method rcv()     { c = n.rcv() & m=ch.e.d[ch.r][c] & ch.r++, m }
    invariant i1() { ch.r <= ch.s }
    invariant i2(a, c) { !ch.e.d[a][c] | a < ch.s }
}|]
    ≈ Hint [Note "uninline calls to ChC"]:
    [prog|
new (const n=n,const e=e,const ch=ChC(n,AEAD(e))) {
    method snd(m)    { ch.snd(m) }
    method rcv()     { ch.rcv() }
}|]
    ≈ Hint [Note "n and e auxiliary"]:
    [prog|
new (const ch=ChC(n,AEAD(e))) {
    method snd(m)    { ch.snd(m) }
    method rcv()     { ch.rcv() }
}|]
    ≈ Hint [ Note "Drop wrapper object"
           , NoInfer
           , fieldsEqual ["ch", "r"] ["r"]
           , fieldsEqual ["ch", "s"] ["s"]
           , fieldsEqual ["ch", "e", "d"] ["e", "d"] ]:
    [prog| ChC(n, AEAD(e)) |]
    : []
