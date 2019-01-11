;; Begin Prelude

(set-option :smt.auto-config false) ; disable automatic self configuration in favor of pattern/trigger-based instantiation
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation in favor of pattern/trigger-based instantiation

(declare-datatypes ((Value 0) (Values 0))
                   (((VInt (val Int))
                     VNil
                     (VSet (valSet (Array Value Bool)))
                     (VMap (valMap (Array Value Value)))
                     (VTuple (elts Values)))
                    (nil (cons (hd Value) (tl Values)))
                    ))

(declare-datatypes ((Valuess 0))
                   ((nils (conss (hds Values) (tls Valuess)))))

(declare-fun deref (Value String) Value)

;; Trying to call any method on the empty message (0) always results in 0.
(assert (forall ((s String))
                (= (deref (VInt 0) s) (VInt 0))))

;; Addresses can be potentially coerced to any value...
(declare-fun vref (Int) Value)

;; as long they don't collide with previous addresses.
;; This is a trick to avoid the quadratic number of trigger instantiations that
;; would result from a conventional encoding of injectivity.
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

; ;;; Maps embedded as z3 arrays:
(define-fun empty-map () (Array Value Value)
  ((as const (Array Value Value)) (VInt 0)))

(declare-fun to-map (Value) (Array Value Value))
(assert (= (to-map (VInt 0)) empty-map))
(assert (forall ((m (Array Value Value)))
                (= (to-map (VMap m)) m)))

(define-fun insert ((k Value) (v Value) (m Value)) Value
  (VMap (store (to-map m) k v)))

(define-fun lookup ((k Value) (m Value)) Value
  (select (to-map m) k))

(declare-fun combine-decl (Value Value) Value)

(define-fun combine ((v Value) (w Value)) Value
  (ite (= (VInt 0) v)
       w
       v))
(assert (forall ((v Value) (w Value))
                (= (combine-decl v w)
                   (combine v w))))

(define-fun munion ((k Value) (v Value)) Value
  (VMap ((_ map (combine-decl (Value Value) Value)) (to-map k) (to-map v))))

(define-fun is-submap-internal ((m1 (Array Value Value)) (m2 (Array Value Value))) Bool
  (forall ((k Value))
          (=> (= (select m2 k) (VInt 0))
              (= (select m1 k) (VInt 0)))))

(define-fun is-submap ((v Value) (w Value)) Value
  (ite (is-submap-internal (to-map v) (to-map w))
       (VInt 1)
       (VInt 0)))

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

(define-fun lt ((v Value) (w Value)) Value
  (ite (< (to-int v) (to-int w))
       (VInt 1)
       (VInt 0)))

(define-fun le ((v Value) (w Value)) Value
  (ite (<= (to-int v) (to-int w))
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
(assert (forall ((a Int) (b Int))
                (= (length (vref a))
                   (length (vref b)))))

(define-fun Z ((v Value)) Value
  (zeroes (length v)))

;; Tuple projection:
(declare-fun proj (Value Value) Value)

;; Sets:
(declare-fun to-set (Value) (Array Value Bool))
(define-fun empty-set () (Array Value Bool)
  ((as const (Array Value Bool)) false))
(assert (= (to-set (VInt 0)) empty-set))
(assert (forall ((set (Array Value Bool)))
                (! (= (to-set (VSet set)) set)
                   :pattern (VSet set))))
;; restrict pattern to (to-set ..) if this turns out to get slow

(define-fun vunion ((v Value) (w Value)) Value
  (VSet ((_ map or) (to-set v) (to-set w))))


(define-fun vmember ((v Value) (w Value)) Value
  (ite (select (to-set w) v)
       (VInt 1)
       (VInt 0)))

(define-fun vintersect ((v Value) (w Value)) Value
  (VSet ((_ map and) (to-set v) (to-set w))))

;; End Prelude
