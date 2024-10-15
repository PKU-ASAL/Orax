
(set-logic QF_UFBV)
(set-option :produce-models true)

(declare-const y (_ BitVec 8))
(declare-const z (_ BitVec 8))
(declare-const x (_ BitVec 8))

(declare-fun _mul ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))

(assert (bvsgt y (_ bv0 8)))
(assert (bvsgt x y))
(assert (= z (_mul x y)))

(check-sat)
(get-model)