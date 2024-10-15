
(set-logic QF_UFBV)
(set-option :produce-models true)
(declare-cbf LinExpr1_eq1ex ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))

(define-fun and3 ((b1 Bool) (b2 Bool) (b3 Bool)) Bool
    (and (and b1 b2) b3))
    
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(declare-const z (_ BitVec 32))

(assert (= (LinExpr1_eq1ex x y z) (_ bv38 32)))
(assert (or ( not (and (= x (_ bv11 32)) (= y (_ bv39 32)) (= z (_ bv12 32)))) (= (LinExpr1_eq1ex x y z) (_ bv11 32))))
(assert (or (not (and (= x (_ bv3 32)) (= y (_ bv30 32)) (= z (_ bv7 32))) ) (= (LinExpr1_eq1ex x y z) (_ bv3 32))))
(assert (or ( not (and (= x (_ bv29 32)) (= y (_ bv28 32)) (= z (_ bv4 32))) ) (= (LinExpr1_eq1ex x y z) (_ bv4 32))))


(check-sat)
(get-model)
(exit)
