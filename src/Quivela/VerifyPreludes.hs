{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
module Quivela.VerifyPreludes where

import Quivela.Util
-- This file defines the preludes for the z3 and dafny backends so we don't
-- need to worry about paths to these files (if they were placed as actual
-- files somewhere)

-- | Z3 encoding for quivela values and operations on them
z3Prelude :: String
z3Prelude = [heredoc|
(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation

(declare-datatypes ((Value 0) (Values 0) (Valuess 0))
                   (((VInt (val Int))
                     VError
                     VNil
                     (VTuple (elts Values))
                     (VRef (addr Int)))
                    (nil (cons (hd Value) (tl Values)))
                    (nils (conss (hds Values) (tls Valuess)))))
;; Maps:
(declare-fun insert (Value Value Value) Value)
(declare-fun lookup (Value Value) Value)

(assert (forall ((k Value) (v Value) (m Value))
                (not (= (insert k v m) VError))))

(assert (forall ((k Value) (v Value) (m Value))
                (= (lookup k (insert k v m))
                   v)))

(assert (forall ((k Value) (k2 Value) (v Value) (m Value))
                (=> (not (= k k2))
                   (= (lookup k (insert k2 v m))
                      (lookup k m)))))

(assert (forall ((k Value) (k2 Value) (v Value) (v2 Value) (m Value))
                (=> (not (= k k2))
                   (= (insert k v (insert k2 v2 m))
                      (insert k2 v2 (insert k v m))))))

(assert (forall ((k Value) (v Value) (v2 Value) (m Value))
                (= (insert k v (insert k v2 m))
                   (insert k v m))))

;; Arithmetic:
(declare-fun add (Value Value) Value)

(assert (forall ((n Int) (m Int))
                (= (add (VInt n) (VInt m)) (VInt (+ n m)))))

(assert (forall ((v Value) (w Value))
                (=> (not (and (is-VInt v) (is-VInt w)))
                    (= (add v w) VError))))

;; Adversary values:
(declare-fun adversary (Valuess) Value)

;; Tuple projection:
(declare-fun proj (Value Value) Value)

|]

-- | Dafny encoding for quivela values and operations on them
dafnyPrelude :: String
dafnyPrelude = [heredoc|
type Addr = nat
type Var = string

datatype Value = Int(val: int) | Tuple(elts:List<Value>) | Map(vals: List<Pair<Value, Value>>) | Ref(addr: Addr) | Nil() | Error()


// lists
datatype List<T> = Cons(car: T, cdr: List<T>) | LNil
predicate method InList<T(==)>(l: List<T>, x: T)
    decreases l
{
    if l.LNil? then false else
    x == l.car || InList(l.cdr, x)
}
function method Length<T>(l: List<T>): nat
    decreases l
{
    if l.LNil? then 0 else 1 + Length(l.cdr)
}

datatype Option<T> = Some(val: T) | None

function method ListRef<T>(l: List<T>, i: int): Option<T>
    decreases l
{
    if l.LNil? then None else
    if i == 0 then Some(l.car) else ListRef(l.cdr, i-1)
}

lemma lemma_List_Length_Cons<T>(l: List<T>)
    requires Length(l) >= 2
    ensures l.Cons? && l.cdr.Cons?
{}

// Dafny will not fully unfold calls to Length with lists that have non-literal
// elements, even if the structure of the list is known; we work around that
// with this predicate:
predicate LengthPred<T>(xs: List<T>, n: nat)
  decreases n
{
    if (n == 0) then
      xs == LNil
    else
      xs.Cons? && LengthPred(xs.cdr, n-1)
}

lemma HasLength<T>(xs: List<T>, n: nat)
  requires LengthPred(xs, n)
  ensures Length(xs) == n { }

// association lists
datatype Pair<T,U> = Pair(car: T, cdr: U)
// predicate method InAssocList<T(==),U>(l: List<Pair<T,U>>, x: T)
//     decreases l
// {
//     if l.LNil? then false else
//     l.car.car == x || InAssocList(l.cdr, x)
// }
function method AssocGet<T(==),U>(l: List<Pair<T,U>>, x: T): Option<U>
    decreases l
{
    if l.LNil? then None else
    if l.car.car == x then Some(l.car.cdr) else
    AssocGet(l.cdr, x)
}
function method AssocSet<T(==),U>(l: List<Pair<T,U>>, x: T, v: U): List<Pair<T,U>>
{
    Cons(Pair(x, v), l)
}

datatype AdversaryCall = AdversaryCall(args: List<Value>)

function method Append<T>(a: List<T>, b: List<T>): List<T>
    decreases a
{
    if a.LNil? then b else Cons(a.car, Append(a.cdr, b))
}


function method Nth<T>(xs: List<T>, n: nat): T
  decreases n
  requires n < Length(xs)
{
  if n == 0 then xs.car else Nth(xs.cdr, n-1)
}

function method Insert(k: Value, v: Value, m: Value): Value
  ensures Insert(k, v, m) != Error
{
  if m.Map?
    then Map(AssocSet(m.vals, k, v))
  else Map(Cons(Pair(k, v), LNil))
}

function method Lookup(k: Value, m: Value): Value
{
  if m.Map?
    then match AssocGet(m.vals, k)
    case Some(v) => v
    case None => Error
  else Error
}

function method Proj(tup: Value, idx: Value): Value
{
  if tup.Tuple? && idx.Int? && 0 <= idx.val < Length(tup.elts)
    then Nth(tup.elts, idx.val)
  else Error
}

lemma LookupSame()
  ensures forall k: Value, v: Value, m : Value :: Lookup(k, Insert(k, v, m)) == v
{
}

lemma LookupDifferent()
  ensures forall k: Value, k': Value, v: Value, m : Value :: k' != k ==> Lookup(k', Insert(k, v, m)) == Lookup(k', if m.Map? then m else Map(LNil))
{

}

function method Adversary(calls: List<List<Value>>): Value

lemma AssocGet_Cons<K, V>()
    ensures forall k': K, k: K, v: V, xs: List<Pair<K, V>> ::
            AssocGet(Cons(Pair(k, v), xs), k') == if k == k' then Some(v) else AssocGet(xs, k')
{

}


lemma Length_Cons<T>()
    ensures forall x: T, xs: List<T> :: Length(Cons(x, xs)) == 1 + Length(xs)
{

}
|]
