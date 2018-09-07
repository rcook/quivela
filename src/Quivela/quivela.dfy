type Addr = nat
type Var = string

datatype Value = Int(val: int) | Tuple(elts:List<Value>) | Map(vals: List<Pair<Value, Value>>) | Nil()

function method RefInv(v: Value): int

function method Ref(addr: int): Value
  ensures RefInv(Ref(addr)) == addr

function method Deref(obj: Value, field: string): Value


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
  ensures Insert(k, v, m) != Int(0)
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
    case None => Int(0)
  else Int(0)
}

function method Proj(tup: Value, idx: Value): Value
{
  if tup.Tuple? && idx.Int? && 0 <= idx.val < Length(tup.elts)
    then Nth(tup.elts, idx.val)
  else Int(0)
}

function method Add(e1: Value, e2: Value): Value
{
  if e1.Int? && e2.Int? then Int(e1.val + e2.val) else Int(0)
}

function method Sub(e1: Value, e2: Value): Value
{
  if e1.Int? && e2.Int? then Int(e1.val - e2.val) else Int(0)
}

function method Le(e1: Value, e2: Value): Value
{
  if e1.Int? && e2.Int? && e1.val < e2.val then Int(1) else Int(0)
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

// Zeroing out messages
function method ValLength(v: Value): nat

lemma ValLengthAssms()
  ensures ValLength(Int(0)) == 0
  ensures forall v :: v != Int(0) && v != Map(LNil()) ==> ValLength(v) > 0

function method Zeroes(n: nat): Value
  ensures ValLength(Zeroes(n)) == n
  ensures Zeroes(0) == Int(0)

function method Z(m: Value): Value
{
  Zeroes(ValLength(m))
}


lemma Z_sane()
  ensures forall v:Value, w:Value :: ValLength(v) == ValLength(w) ==> Z(v) == Z(w)
  ensures Z(Int(0)) == Int(0)
{
  ValLengthAssms();
}
