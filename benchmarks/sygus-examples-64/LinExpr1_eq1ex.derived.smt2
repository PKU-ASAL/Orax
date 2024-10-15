
(set-logic QF_UFBV)
(set-option :produce-models true)
(declare-cbf LinExpr1_eq1ex ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64)) (_ BitVec 64))

(define-fun and3 ((b1 Bool) (b2 Bool) (b3 Bool)) Bool
    (and (and b1 b2) b3))
    
(declare-const x (_ BitVec 64))
(declare-const y (_ BitVec 64))
(declare-const z (_ BitVec 64))

(assert (= (LinExpr1_eq1ex x y z) (_ bv38 64)))
(assert (=> (and (= x (_ bv11 64)) (= y (_ bv39 64)) (= z (_ bv12 64))) (= (LinExpr1_eq1ex x y z) (_ bv11 64))))
(assert (=> (and (= x (_ bv3 64)) (= y (_ bv30 64)) (= z (_ bv7 64))) (= (LinExpr1_eq1ex x y z) (_ bv3 64))))
(assert (=> (and (= x (_ bv29 64)) (= y (_ bv28 64)) (= z (_ bv4 64))) (= (LinExpr1_eq1ex x y z) (_ bv4 64))))


(check-sat)
(get-model)
(exit)
