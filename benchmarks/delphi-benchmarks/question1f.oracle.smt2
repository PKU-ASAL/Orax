(set-logic QF_UFBV)
(set-option :produce-models true)

;  a number with four prime factors and a multiple of 2 and 7. is unsat
(declare-fun isPrimeLUT ((_ BitVec 8) ) (_ BitVec 8))

(declare-fun n () (_ BitVec 8))
(assert (or (= n (_ bv12 8))(= n  (_ bv8 8))(= n  (_ bv13 8)) (= n  (_ bv17 8))
	    (= n  (_ bv15 8)) (= n  (_ bv21 8)) (= n  (_ bv9 8))(= n  (_ bv10 8))(= n  (_ bv18 8))(= n  (_ bv14 8))(= n  (_ bv16 8))
	    (= n  (_ bv6 8)) ))

(declare-fun multiplier () (_ BitVec 8))
(declare-fun multiplier2 () (_ BitVec 8))
(declare-fun factor1 () (_ BitVec 8))
(declare-fun factor2 () (_ BitVec 8))
(declare-fun factor3 () (_ BitVec 8))
(declare-fun factor4 () (_ BitVec 8))

(assert (= (bvmul  (_ bv2 8) multiplier) n))
(assert (= (bvmul  (_ bv7 8) multiplier2) n))
(assert (= (isPrimeLUT factor1) (_ bv1 8)))
(assert (= (isPrimeLUT factor2) (_ bv1 8)))
(assert (= (isPrimeLUT factor3) (_ bv1 8)))
(assert (= (isPrimeLUT factor4) (_ bv1 8)))

(assert (= (bvmul factor1 factor2 factor3 factor4) n))
(check-sat)
(get-model)

