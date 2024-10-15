
(set-logic QF_UFBV)
(set-option :produce-models true)
(set-option :simplification none)


(declare-fun _mul ((_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))

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

(assert (= r (bvmul p q)))

(check-sat)
(get-model)