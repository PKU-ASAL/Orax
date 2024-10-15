
(set-logic QF_UFBV)
(set-option :produce-models true)
(set-option :simplification none)

(declare-const y (_ BitVec 32))
(declare-const z (_ BitVec 32))
(declare-const x (_ BitVec 32))

(declare-fun _mul ((_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))

(assert (bvugt z (_ bv256 32)))
(assert (bvult z (_ bv65536 32)))
(assert (bvugt x y))
(assert (= z (_mul x y)))

(check-sat)
(get-model)