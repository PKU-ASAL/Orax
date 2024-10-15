(set-logic QF_UFBV)
(set-option :produce-models true)

(declare-fun isSquare ( (_ BitVec 8) ) (_ BitVec 8))

(declare-fun n () (_ BitVec 8))
(assert (or (= n (_ bv12 8))(= n (_ bv8 8))(= n (_ bv13 8)) (= n (_ bv17 8)) (= n (_ bv15 8))
	    (= n (_ bv21 8)) (= n (_ bv9 8))(= n (_ bv10 8))(= n (_ bv18 8))
	    (= n (_ bv14 8))(= n (_ bv16 8))(= n (_ bv6 8)) ))

;(declare-fun root () (_ BitVec 8))
;(assert (= (bvmul root root) n))

(assert (= (isSquare n) (_ bv1 8)))
(assert (= (bvurem n (_ bv2 8)) (_ bv1 8)))

(check-sat)
(get-model)
