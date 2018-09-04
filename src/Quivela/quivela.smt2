(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation

(declare-datatypes ((Value 0) (Values 0) (Valuess 0))
                   (((VInt (val Int))
                     VError
                     VNil
                     (VTuple (elts Values)))
                    (nil (cons (hd Value) (tl Values)))
                    (nils (conss (hds Values) (tls Valuess)))))

(declare-fun deref (Value String) Value)

;; Addresses can be potentially coerced to any value
(declare-fun vref (Int) Value)

;; as long they don't collide with previous addresses
;; Trick to avoid quadratic number of trigger instantiantions that
;; would result from a conventional encoding of injectivity
(declare-fun vref-inv (Value) Int)
(assert (forall ((a Int))
                (! (= (vref-inv (vref a)) a)
                   :pattern (vref a))))

;; Since programs can only obtain references from new() expressions,
;; and we assume these are bitstrings of the length of the security parameter,
;; they are never the empty bitstring (i.e. VError)
(assert (forall ((a Int))
                (not (= (vref a) VError))))


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

(declare-fun sub (Value Value) Value)

(assert (forall ((n Int) (m Int))
                (= (sub (VInt n) (VInt m)) (VInt (- n m)))))

(assert (forall ((v Value) (w Value))
                (=> (not (and (is-VInt v) (is-VInt w)))
                    (= (sub v w) VError))))

(declare-fun mul (Value Value) Value)

(assert (forall ((n Int) (m Int))
                (= (mul (VInt n) (VInt m)) (VInt (* n m)))))

(assert (forall ((v Value) (w Value))
                (=> (not (and (is-VInt v) (is-VInt w)))
                    (= (mul v w) VError))))

(declare-fun divi (Value Value) Value)

(assert (forall ((n Int) (m Int))
                (= (divi (VInt n) (VInt m)) (VInt (/ n m)))))

(assert (forall ((v Value) (w Value))
                (=> (not (and (is-VInt v) (is-VInt w)))
                    (= (divi v w) VError))))

(declare-fun le (Value Value) Value)

(assert (forall ((n Int) (m Int))
                (and (=> (= (le (VInt n) (VInt m)) (VInt 1))
                         (< n m))
                     (=> (< n m)
                         (= (le (VInt n) (VInt m))
                            (VInt 1))))))

(assert (forall ((n Int) (m Int))
                (and (=> (= (le (VInt n) (VInt m)) VError)
                         (not (< n m)))
                     (=> (not (< n m))
                         (= (le (VInt n) (VInt m))
                            VError)))))

(assert (forall ((v Value) (w Value))
                (=> (not (and (is-VInt v) (is-VInt w)))
                    (= (le v w) VError))))

;; Adversary values:
(declare-fun adversary (Valuess) Value)

;; Tuple projection:
(declare-fun proj (Value Value) Value)
