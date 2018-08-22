(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation
;; (declare-datatypes () ((Value (VInt (val Int))
;;                               VError
;;                               VNil
;;                               (VTuple (elts Values))
;;                               (VRef (addr Int)))
;;                        (Values nil (cons (hd Value) (tl Values)))
;;                        (Valuess nils (conss (hds Values) (tls Valuess)))))

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
;;
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

;; Adversary values:
(declare-fun adversary (Valuess) Value)

(assert (forall ((vss Valuess) (vss2 Valuess))
                (= (adversary vss) (adversary vss2))))

;; Tuple projection:
(declare-fun proj (Value Value) Value)
;; (declare-const v Value)
;; (declare-const v2 Value)
;; (declare-const v3 Value)
;; (assert (not (= (lookup v (insert v v2 v3))
;;                 v2)))
