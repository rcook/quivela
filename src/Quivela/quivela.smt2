(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation

(declare-datatypes ((Value 0) (Values 0) (Valuess 0))
                   (((VInt (val Int))
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
;; they are never the empty bitstring (i.e. (VInt 0))
(assert (forall ((a Int))
                (not (= (vref a) (VInt 0)))))


;; Maps:
(declare-fun insert (Value Value Value) Value)
(declare-fun lookup (Value Value) Value)

(assert (forall ((k Value) (v Value) (m Value))
                (not (= (insert k v m) (VInt 0)))))

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
;; Interpreting a value as an integer:
(declare-fun to-int (Value) Int)
(assert (forall ((n Int)) (= (to-int (VInt n)) n)))

(define-fun add ((v Value) (w Value)) Value
  (VInt (+ (to-int v) (to-int w))))

(define-fun sub ((v Value) (w Value)) Value
  (VInt (- (to-int v) (to-int w))))

(define-fun mul ((v Value) (w Value)) Value
  (VInt (* (to-int v) (to-int w))))

(define-fun divi ((v Value) (w Value)) Value
  (VInt (/ (to-int v) (to-int w))))

(define-fun le ((v Value) (w Value)) Value
  (ite (< (to-int v) (to-int w))
       (VInt 1)
       (VInt 0)))

;; Adversary values:
(declare-fun adversary (Valuess) Value)


;; Zeroing out messages:
;; We assume this gives us a value representing a bitstring of n zeroes
(declare-fun zeroes (Int) Value)

(declare-fun length (Value) Int)

(assert (forall ((n Int)) (= (length (zeroes n)) n)))

(assert (= (length (VInt 0)) 0))
(assert (forall ((v Value)) (>= (length v) 0)))
(assert (forall ((v Value))
                (=> (not (= v (VInt 0)))
                   (> (length v) 0))))

(define-fun Z ((v Value)) Value
  (zeroes (length v)))

;; Tuple projection:
(declare-fun proj (Value Value) Value)
