
(set-logic QF_UFBV)
(set-option :produce-models true)

(declare-oracle-fun _mul ./mulOracle ((_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))

(define-fun ispow2 ((x (_ BitVec 32))) Bool 
  (= (_ bv0 32) (bvand x (bvsub x (_ bv1 32)))))


(declare-const p (_ BitVec 32))
(declare-const q (_ BitVec 32))
(declare-const r (_ BitVec 32))

(declare-const y (_ BitVec 32))
(declare-const z (_ BitVec 32))
(declare-const x (_ BitVec 32))


(assert (bvult (_ bv255 32) z))
(assert (bvult z (_ bv65536 32)))
(assert (bvugt x y))
(assert (= z (_mul x y)))

(assert (and (ispow2 p) (ispow2 q) (ispow2 r)))
(assert (and (bvugt p (_ bv1 32)) (bvugt q (_ bv1 32)) (bvugt r (_ bv1 32)) ) )
(assert (= (_ bv64 32) (bvmul p q r)))

(check-sat)
