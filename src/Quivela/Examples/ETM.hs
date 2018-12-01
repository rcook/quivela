-- Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
-- SPDX-License-Identifier: Apache-2.0
{-# LANGUAGE QuasiQuotes, TemplateHaskell #-}

module Quivela.Examples.ETM
  ( program
  ) where

import Control.Lens hiding (rewrite)
import Quivela

program =
  prove'
    emptyVerifyEnv
    ([prog'|
method MacI(mac) {
    new (const mac=mac,tg=0) {
        method tag(m) { tg[m] = mac.tag(m) }
        method verify(m,t) { t & tg[m] == t }
    }
}

// _e freshly encrypts iff _e ~ Enc(_e)

method Enc(e) {
    new (const e=e, d=0) {
        method enc(m) { c = e.enc(m) & !d[c] & d[c] = m & c }
        method dec(c) { e.dec(c) }
    }
}


// _e is a CPA-secure encryptor iff CpaC(_e) ~ CpaI(_e)

method CpaC(e) {
    new (const e=e,h=0) {
        method enc(m) { c = e.enc(m) & h[c]=1 & c }
        method dec(c) { h[c] & e.dec(c) }
    }
}

method CpaI(e) {
    new (const e=e,d=0) {
        method enc(m) { c = e.enc(Z(m)) & d[c] = m & c }
        method dec(c) { d[c] }
    }
}

// _e is an AEAD encryptor iff _e ~ AeadI(_e)

method AeadI(e) {
    new (const e=e,d=0) {
        method enc(a,m) { c = e.enc(a,Z(m)) & d[<a,c>] = m & c }
        method dec(a,c) { d[<a,c>] }
    }
}


// concrete encrypt-then-mac

method EtM(e,mac) {
    new (const e=e, const mac=mac) {
        method enc(a,m) {
            m &
            em = e.enc(m) &
            t = mac.tag(<a,em>) &
            <em,t>
        }
        method dec(a,c) {
            <em, t> = c &
            c &
            mac.verify(<a,em>,t) &
            e.dec(em)
        }
    }
}

_e = adversary()
_mac = adversary()

assume _e ≈ Enc(_e)
assume _mac ≈ MacI(_mac)
assume CpaI(_e) ≈ CpaC(_e)

|]) $
  let mac_tg = fieldEqual ["mac", "tg"]
      cpa_d = fieldEqual ["cpa", "d"]
      d = fieldEqual ["d"]
      e_d = fieldEqual ["e", "d"]
      cpa_h = fieldEqual ["cpa", "h"]
   in [prog| EtM(_e,_mac) |] ≈ Hint [Note "Unfold definition of EtM"] :
      [prog|
new (const e=_e, const mac=_mac) {
    method enc(a, m) { m & em = e.enc(m) & t = mac.tag(<a,em>) & <em,t> }
    method dec(a, c) { <em,t> = c, c & mac.verify(<a,em>,t) & e.dec(em) }
}
|] ≈
      Hint [rewrite "_mac" "MacI(_mac)"] :
      [prog|
new (const e=_e, const mac=MacI(_mac)) {
    method enc(a, m) { m & em = e.enc(m) & t = mac.tag(<a,em>) & <em,t> }
    method dec(a, c) { <em,t> = c, c & mac.verify(<a,em>,t) & e.dec(em) }
}|] ≈
      Hint [Note "Introducing cpa"] :
      [prog|
new (..., const cpa=new(const e=_e) {
        method enc(m) { e.enc(m) }
        method dec(c) { e.dec(c) }
    }) { ... }
|] ≈
      Hint [Note "Replace calls to e by calls to cpa"] :
      [prog|
    method enc(a, m) { m & em = cpa.enc(m) & t = mac.tag(<a,em>) & <em,t> }
    method dec(a, c) { <em,t> = c, c & mac.verify(<a,em>,t) & cpa.dec(em) }
|] ≈
      Hint [Note "Store ciphertext in h map"] :
      [prog|
new (..., const cpa=new(const e=_e,h=0) {
        method enc(m) { c = e.enc(m) & h[c] = 1 & c }
        method dec(c) { e.dec(c) }
    }) { ...
    invariant inv1(a, em) { !mac.tg[<a, em>] | cpa.h[em] }
}|] ≈
      Hint [Note "Ensure ciphertext in h before decryption"] :
      [prog|
    method dec(a, c) { <em,t> = c, c & mac.verify(<a,em>,t) & cpa.h[em] & cpa.dec(em) }
|] ≈
      Hint [Note "Move h lookup into cpa object"] :
      [prog|
new (..., const cpa=new(const e=_e,h=0) {
        method enc(m) { c = e.enc(m) & h[c] = 1 & c }
        method dec(c) { h[c] & e.dec(c) }
    }) {...
    method dec(a, c) { <em,t> = c, c & mac.verify(<a,em>,t) & cpa.dec(em) }
    delete inv1
}|] ≈
      Hint [Note "Fold definition of CpaC"] :
      [prog|
new (..., const cpa=CpaC(_e)) { ... }|] ≈
      Hint [Note "Delete unused e field"] :
      [prog|
new (..., delete e) { ... }|] ≈
      Hint [rewrite "CpaC(_e)" "CpaI(_e)"] :
      [prog|
new (..., const cpa=CpaI(_e)) { ... } |] ≈
      Hint [Note "Reintroduce e"] :
      [prog|
new (..., const e=_e) { ... }|] ≈
      Hint [Note "Look up ciphertext in map instead of calling decrypt"] :
      [prog|
    method enc(a, m) { m & em = e.enc(Z(m)) & cpa.d[em] = m & t = mac.tag(<a,em>) & <em,t> }
    method dec(a, c) { <em,t> = c, c & mac.verify(<a,em>,t) & cpa.d[em] } |] ≈
      Hint [Note "Introduce d"] :
      [prog|
new (..., d=0) {...
    method enc(a, m) { m & em = e.enc(Z(m)) & cpa.d[em] = m & t = mac.tag(<a,em>) & d[<a,<em,t>>] = m & <em,t> }
}|] ≈
      Hint [rewrite "_e" "Enc(_e)"] :
      [prog|
new (const mac=MacI(_mac),const cpa=CpaI(Enc(_e)), const e=Enc(_e), d=0) {
    method enc(a,m) { m & em = e.enc(Z(m)) & cpa.d[em] = m & t = mac.tag(<a,em>) & d[<a,<em,t>>] = m & <em,t> }
    method dec(a,c) { <em,t> = c, c & mac.verify(<a,em>,t) & cpa.d[em] }
}|] ≈
      Hint [Note "Look up ciphertext in new d map"] :
      [prog|
     method dec(a:*,c) { <em, t> = c, c & mac.verify(<a,em>,t) & cpa.d[em] & d[<a,<em,t>>] }
     invariant inv1(a, em, t) { d[<a, <em, t>>] == (t & (mac.tg[<a, em>] == t) & cpa.d[em]) }
     invariant inv2(a, em, t) { (!mac.tg[<a, em>]) | (cpa.d[em] & e.d[em]) }
|] ≈
      Hint [Note "Lookup in d to decrypt", NoInfer, mac_tg, e_d, d, cpa_d] :
      [prog|
      delete inv1
      delete inv2
      method dec(a, c) { d[<a,c>] }
      invariant inv3(a, em, t) { (!d[<a, <em, t>>]) | (t & ((t == mac.tg[<a, em>]) & (cpa.d[em] == d[<a, <em, t>>])) & e.d[em]) }
|] ≈
      Hint [Note "Drop invariant", NoInfer, mac_tg, e_d, d, cpa_d] :
      [prog|
      delete inv3
|] ≈
      Hint [rewrite "Enc(_e)" "_e"] :
      [prog|
  new (const mac=MacI(_mac),const cpa=CpaI(_e),const e=_e,d=0) {
      method enc(a, m) { m & em = e.enc(Z(m)) & cpa.d[em] = m & t = mac.tag(<a,em>) & d[<a,<em,t>>] = m & <em,t> }
      method dec(a, c) { d[<a,c>] }
  }|] ≈
      Hint [Note "cpa unused"] :
      [prog|
  new (..., delete cpa) {...
      method enc(a, m) { m & em = e.enc(Z(m)) & em & t = mac.tag(<a,em>) & d[<a,<em,t>>] = m & <em,t> }
  }|] ≈
      Hint [rewrite "MacI(_mac)" "_mac"] :
      [prog|
  new (const mac=_mac, const e=_e, d=0) {
      method enc(a, m) { m & em = e.enc(Z(m)) & em & t = mac.tag(<a,em>) & d[<a,<em,t>>] = m & <em,t> }
      method dec(a, c) { d[<a,c>] }
  }|] ≈
      Hint [Note "Factor out operations into e"] :
      [prog|
  new (const e=(new(const e=_e,const mac=_mac) {
          method enc(a, m) { m & em = e.enc(m) & em & t = mac.tag(<a,em>) & <em,t> }
          method dec(a, c) { em = c`0,  t = c`1,  mac.verify(<a, em>, t) & e.dec(em) }
      }), d=0) {
      method enc(a, m) { c=e.enc(a, Z(m)) & d[<a,c>] = m & c }
      method dec(a, c) { d[<a,c>] }
  }|] ≈ -- Hint [d]:
      [prog| AeadI(EtM(_e,_mac)) |] :
      []
