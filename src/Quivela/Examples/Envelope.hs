{-# LANGUAGE QuasiQuotes, TemplateHaskell #-}
module Env where

import Control.Lens hiding (rewrite)
import Quivela

prove (set useCache False emptyVerifyEnv)
  [prog'|
method skenc(k, a, m) { rnd() }
method skdec(k, a, c) { rnd() }

method Enc(e) { new (const e,d=0) {
   method enc(a,m)      { c = e.enc(a,Z(m)) & d[a][c] = <m> & c } // do we need to add the !d[a][c] check?
   method dec(a,c)      { d[a][c] }
}}

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


method EncL(e) { new (const e=e,d) {
    method enc(a,m)      { c = e.enc(a,Z(m)) & d[a][c] = <m> & c }
}}

method EncLI(e) { new (const e=e) {
    method enc(a,m)      { e.enc(a,Z(m)) }
}}
e = adversary()
|] $
    [prog|
         Enc(Env(Enc(e))) |]
    ≈ Hint [Note "defs"]:
    [prog|
new (const e = Env(Enc(e)),d=0) {
  method enc(a,m)      { c = e.enc(a,Z(m)) & d[a][c] = <m> & c }
  method dec(a,c)      { d[a][c] }
}|]
   ≈ Hint [Note "defs, renaming e"]:
   [prog|
new (const e = Enc(e),d=0) {
  method enc(a,m)      { k=rnd() & ek = e.enc(0,k) & em = skenc(k,a,Z(m)) & c = <ek,em> & d[a][c] = <m> & c }
  method dec(a,c)      { d[a][c] }
}|]
   ≈ Hint [Note "switching from Enc to EncL since no calls to dec"]:
   [prog|
new (const e = EncL(e),d=0) {
  method enc(a,m)      { k=rnd() & ek = e.enc(0,k) & em = skenc(k,a,Z(m)) & c = <ek,em> & d[a][c] = <m> & c }
  method dec(a,c)      { d[a][c] }
}|]
   ≈ Hint [Note "assumption", rewrite "EncL(e)" "EncLI(e)"]:
   [prog|
new (const e = EncLI(e),d=0) {
  method enc(a,m)      { k=rnd() & ek = e.enc(0,k) & em = skenc(k,a,Z(m)) & c = <ek,em> & d[a][c] = <m> & c }
  method dec(a,c)      { d[a][c] }
}|]
   ≈ Hint [Note "def e.enc; Z(k) ~ zk"]:
   [prog|
new (const e = EncLI(e),d=0) {
  method enc(a,m)      { k=rnd() & ek = e.e.enc(0,Z(k)) & em = skenc(k,a,Z(m)) & c = <ek,em> & d[a][c] = <m> & c }
// orig: enc(a,m)      { k=rnd() & ek = e.enc(0,zk) & em = skEnc(k,a,Z(m)) & c = <ek,em> & d[a][c] = <m> & c }
  method dec(a,c)      { d[a][c] }
}|]
  ≈ Hint [Note "introducing f; def E"]:
  [prog|
new (const e = EncLI(e),d=0) {
  method enc(a,m)      { f = E() & ek = e.e.enc(0,Z(f.k)) & em = f.enc(a,Z(m)) & c = <ek,em> & d[a][c] = <m> & c }
// orig: enc(a,m)      { f = E() & ek = e.enc(0,zk) & em = f.enc(a,Z(m)) & c = <ek,em> & d[a][c] = <m> & c }
  method dec(a,c)      { d[a][c] }
}|]
  ≈ Hint [Note "assumption", rewrite "E()" "Enc(E())"]:
  [prog|
new (const e = EncLI(e),d=0) {
  method enc(a,m)      { f = Enc(E()) & ek = e.e.enc(0,Z(f.k)) & em = f.enc(a,Z(m)) & c = <ek,em> & d[a][c] = <m> & c }
  method dec(a,c)      { d[a][c] }
}|]
  ≈ Hint [Note "similar to above (f.dec not called) - replace Enc(E()) w EncLI(E()), then Z(m) w. m, then EncLI(E()) w. Enc(E())"]:
  [prog|
new (const e = EncLI(e),d=0) {
  method enc(a,m)      { f = Enc(E()) & ek = e.e.enc(0,Z(f.k)) & em = f.enc(a,m) & c = <ek,em> & d[a][c] = <m> & c }
  method dec(a,c)      { d[a][c] }
}|]
     :[]
     {-
~ // introducing fs

new (e = EncLI(e),d=0,fs=0) {

       enc(a,m)      { f = Enc(E()) & ek = e.enc(0,zk) & em = f.enc(a,m) & fs[ek]=f & c = <ek,em> & d[a][c] = <m> & c }

       dec(a,c)      { d[a][c] }

}

~ // invariant(a,c) { !d[a][c] | <ek,em> = d[a][c] & 1 }

new (e = EncLI(e),d=0,fs=0) {

       enc(a,m)      { f = Enc(E()) & ek = e.enc(0,zk) & em = f.enc(a,m) & fs[ek]=f & c = <ek,em> & d[a][c] = <m> & c }

       dec(a,c)      { <ek,em> = c & d[a][c] }

}

~ // invariant(a,ek,em) { d[a][<ek,em>] == fs[ek].d[a][em] }

new (e = EncLI(e),fs=0) {

       enc(a,m)      { f = Enc(E()) & ek = e.enc(0,zk) & em = f.enc(a,m) & fs[ek]=f & c = <ek,em> & d[a][c] = <m> & c }

       dec(a,c)      { <ek,em> = c & fs[ek].dec(a,em) }

}

~ // d auxilliary

new (e = EncLI(e),fs=0) {

       enc(a,m)      { f = Enc(E()) & ek = e.enc(0,zk) & em = f.enc(a,m) & fs[ek]=f & <ek,em> }

       dec(a,c)      { <ek,em> = c & fs[ek].dec(a,em) }

}

~ // Enc(E()) ~ E()

new (e = EncLI(e),fs=0) {

       enc(a,m)      { f = E() & ek = e.enc(0,zk) & em = f.enc(a,m) & fs[ek]=f & <ek,em> }

       dec(a,c)      { <ek,em> = c & fs[ek].dec(a,em) }

}

~ // zk ~ Z(f.k)

new (e = EncLI(e),fs=0) {

       enc(a,m)      { f = E() & ek = e.enc(0,f.k) & em = f.enc(a,m) & fs[ek]=f & <ek,em> }

       dec(a,c)      { <ek,em> = c & fs[ek].dec(a,em) }

}

~ // EncLI(e) ~ EncL(e); switching from EncL to Enc

new (e = EncLI(e),fs=0) {

       enc(a,m)      { f = E() & ek = e.enc(0,f.k) & em = f.enc(a,m) & fs[ek]=f & <ek,em> }

       dec(a,c)      { <ek,em> = c & fs[ek].dec(a,em) }

}

~ // invariant(ek) { fs[ek].k == e.d[0][ek]) }; type of fs

new (e = Enc(e),fs=0) {

       enc(a,m)      { f = E() & ek = e.enc(0,f.k) & em = f.enc(a,m) & fs[ek]=f & <ek,em> }

       dec(a,c)      { <ek,em> = c & k = e.dec(0,ek) & skDec(k,a,em) }

}

~ // fs auxilliary

new (e = Enc(e)) {

       enc(a,m)      { f = E() & ek = e.enc(0,f.k) & em = f.enc(a,m) & <ek,em> }

       dec(a,c)      { <ek,em> = c & k = e.dec(0,ek) & skDec(k,a,em) }

}

~ // inlining

new (e = Enc(e)) {

       enc(a,m)      { k = rnd() & ek = e.enc(0,k) & em = skEnc(k,a,m) & <ek,em> }

       dec(a,c)      { <ek,em> = c & k = e.dec(0,ek) & skDec(k,a,em) }

}

~ // defs

Env(Enc(e))

       }
-}
