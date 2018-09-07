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
   ≈ Hint (NoInfer : eqs) :
   [prog|
new (const n=ChC(n,AEAD(e)),s=0,r=0,h=0) {
    method snd(m)    { h[s++] = <m>, n.snd(Z(m)), 1 }
    method rcv()     { n.rcv() & r<s & h[r++] }
}|]
   ≈ Hint (NoInfer : directEqs ++
           map (\chanField -> fieldsEqual chanField ("ch" : tail chanField)) channelFields): -- renaming n to ch, caching ch.n as n, ch.e.e as e
   [prog|
new (const n=n,const e=e,const ch=ChC(n,AEAD(e)),s=0,r=0,h=0) {
    method snd(m)    { h[s++] = <m>, ch.snd(Z(m)), 1 }
    method rcv()     { ch.rcv() & r<s & h[r++] }

}|]
   ≈ let renamedChannelEqs = map (\chanField -> fieldEqual ("ch" : tail chanField)) channelFields
     in Hint (NoInfer : directEqs ++ renamedChannelEqs): -- inlining
   [prog|
new (const n=n, const e=e,const ch=ChC(n,AEAD(e)),s=0,r=0,h=0) {
    method snd(m)    { h[s++] = <m>, (c = ch.e.enc(ch.s,Z(m)) & n.snd(c) & ch.s++, 1), 1 }
    method rcv()     { (c = n.rcv() & m=ch.e.d[ch.r][c] & ch.r++, m) & r<s & h[r++] }

}|]
   ≈ Hint (NoInfer : directEqs ++ renamedChannelEqs):
   [prog|
new (const n=n,const e=e,const ch=ChC(n,AEAD(e)),s=0,r=0,h=0) {
    method snd(m)    { h[s++] = <m>, ((c = e.enc(ch.s,Z(m)) & ch.e.d[ch.s][c] = <Z(m)> & c) & n.snd(c) & ch.s++, 1), 1 }
    method rcv()     { c = n.rcv() & m=ch.e.d[ch.r][c] & ch.r++, r<s & h[r++] }
}|]
   ≈ let commonInvs = map fieldEqual [["ch", "r"], ["ch", "s"], ["ch", "e", "d"], ["s"], ["r"], ["h"]]
     in Hint (NoInfer : commonInvs):
   [prog|
new (const n=n,const e=e,const ch=ChC(n,AEAD(e)),s=0,r=0,h=0) {
    method snd(m)    { h[s++] = <m>, (c = e.enc(ch.s,Z(m)) & ch.e.d[ch.s][c] = <Z(m)> & n.snd(c) & ch.s++), 1 }
    method rcv()     { c = n.rcv() & m=ch.e.d[ch.r][c] & ch.r++, r<s & h[r++] }
}|]
    ≈ Hint ([NoInfer] ++ directEqs ++ renamedChannelEqs):
   [prog|
new (const n=n,const e=e,const ch=ChC(n,AEAD(e)),s=0,r=0,h=0) {
    method snd(m)    { (c = e.enc(ch.s,Z(m)) & n.snd(c) & h[s++] = <m> & ch.e.d[ch.s][c] = <Z(m)> & ch.s++), 1 }
    method rcv()     { c = n.rcv() & m=ch.e.d[ch.r][c] & r<s & ch.r++, r<s & h[r++] }
    invariant iS()     { ch.s == s }
    invariant iR()     { ch.r == r }
}|]
    ≈ Hint ([NoInfer] ++ directEqs ++ renamedChannelEqs):
    [prog|
new (const n=n,const e=e,const ch=ChC(n,AEAD(e)),s=0,r=0,h=0) {
    method snd(m)    { (c = e.enc(ch.s,Z(m)) & n.snd(c) & h[ch.s] = <m> & ch.e.d[ch.s][c] = <Z(m)> & ch.s++), 1 }
    method rcv()     { c = n.rcv() & m=ch.e.d[ch.r][c] & ch.r<ch.s & ch.r++, (ch.r-1)<ch.s & h[ch.r-1] }
}|]
    ≈ Hint ([NoInfer] ++ [fieldEqual ["h"]] ++ renamedChannelEqs):
    [prog|
new (const n=n,const e=e,const ch=ChC(n,AEAD(e)),h=0) {
    method snd(m)    { (c = e.enc(ch.s,Z(m)) & n.snd(c) & h[ch.s] = <m> & ch.e.d[ch.s][c] = <Z(m)> & ch.s++), 1 }
    method rcv()     { c = n.rcv() & m=ch.e.d[ch.r][c] & ch.r<ch.s & ch.r++, (ch.r-1)<ch.s & h[ch.r-1] }
    invariant i1() { ch.r <= ch.s }
    invariant i2(a, c) { !ch.e.d[a][c] | a < ch.s }
}|]
    ≈ Hint ([NoInfer] ++ [fieldEqual ["h"]] ++ renamedChannelEqs):
    [prog|
new (const n=n,const e=e,const ch=ChC(n,AEAD(e)),h=0) {
    method snd(m)    { (c = e.enc(ch.s,Z(m)) & n.snd(c) & h[ch.s] = <m> & ch.e.d[ch.s][c] = <Z(m)> & ch.s++), 1 }
    method rcv()     { c = n.rcv() & m=ch.e.d[ch.r][c] & ch.r++, h[ch.r-1] }
    invariant i1() { ch.r <= ch.s }
    invariant i2(a, c) { !ch.e.d[a][c] | a < ch.s }
}|]
    ≈ Hint ([NoInfer] ++ [fieldEqual ["h"]] ++ renamedChannelEqs):
    [prog|
new (const n=n,const e=e,const ch=ChC(n,AEAD(e)),h=0) {
    method snd(m)    { (c = e.enc(ch.s,Z(m)) & n.snd(c) & h[ch.s] = <m> & ch.e.d[ch.s][c] = <m> & ch.s++), 1 }
    method rcv()     { c = n.rcv() & m=ch.e.d[ch.r][c] & ch.r++, h[ch.r-1] }
    invariant i1() { ch.r <= ch.s }
    invariant i2(a, c) { !ch.e.d[a][c] | a < ch.s }
    invariant i3(a, c) { !ch.e.d[a][c] | h[a] == ch.e.d[a][c] }
}|]
    ≈ Hint ([NoInfer] ++ [fieldEqual ["h"]] ++ renamedChannelEqs):
    [prog|
new (const n=n,const e=e,const ch=ChC(n,AEAD(e)),h=0) {
    method snd(m)    { (c = e.enc(ch.s,Z(m)) & n.snd(c) & h[ch.s] = <m> & ch.e.d[ch.s][c] = <m> & ch.s++), 1 }
    method rcv()     { c = n.rcv() & m=ch.e.d[ch.r][c] & ch.r++, m }
    invariant i1() { ch.r <= ch.s }
    invariant i2(a, c) { !ch.e.d[a][c] | a < ch.s }
    invariant i3(a, c) { !ch.e.d[a][c] | h[a] == ch.e.d[a][c] }
}|]
    ≈ Hint ([NoInfer] ++ renamedChannelEqs):
    [prog|
new (const n=n,const e=e,const ch=ChC(n,AEAD(e))) {
    method snd(m)    { (c = e.enc(ch.s,Z(m)) & n.snd(c) & ch.e.d[ch.s][c] = <m> & ch.s++), 1 }
    method rcv()     { c = n.rcv() & m=ch.e.d[ch.r][c] & ch.r++, m }
    invariant i1() { ch.r <= ch.s }
    invariant i2(a, c) { !ch.e.d[a][c] | a < ch.s }
}|]
    ≈ Hint ([NoInfer] ++ renamedChannelEqs):
    [prog|
new (const n=n,const e=e,const ch=ChC(n,AEAD(e))) {
    method snd(m)    { ch.snd(m) }
    method rcv()     { ch.rcv() }
}|]
    ≈ Hint ([NoInfer] ++ renamedChannelEqs):
    [prog|
new (const ch=ChC(n,AEAD(e))) {
    method snd(m)    { ch.snd(m) }
    method rcv()     { ch.rcv() }
}|]
    ≈ Hint [ NoInfer
           , fieldsEqual ["ch", "r"] ["r"]
           , fieldsEqual ["ch", "s"] ["s"]
           , fieldsEqual ["ch", "e", "d"] ["e", "d"] ]:
    [prog| ChC(n, AEAD(e)) |]
    : []
