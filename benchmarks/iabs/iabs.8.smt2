(set-logic QF_UFBV)
(set-option :produce-models true)
;; (set-option :simplification none)

(declare-cbf iabs ((_ BitVec 8)) (_ BitVec 8))

(declare-fun x10 () (_ BitVec 8))
(declare-const x34 (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-const tempx (_ BitVec 8))

(assert ( = (iabs x10) tempx))
(assert ( bvsgt tempx (_ bv0 8)))
(assert (= x34 (bvmul (_ bv2 8) y)))
(assert (bvsgt x10 x34))

(check-sat)
(get-model)