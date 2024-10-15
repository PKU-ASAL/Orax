(set-logic QF_UFBV)
(set-option :produce-models true)

(declare-fun isPrimeLUT ((_ BitVec 8) ) (_ BitVec 8))


(declare-fun factor1 () (_ BitVec 8))
(declare-fun factor2 () (_ BitVec 8))
(declare-fun factor3 () (_ BitVec 8))
(declare-fun factor4 () (_ BitVec 8))
(declare-fun factor5 () (_ BitVec 8))
(declare-fun factor6 () (_ BitVec 8))

(assert (= (isPrimeLUT factor1) (_ bv1 8)))
(assert (= (isPrimeLUT factor2) (_ bv1 8)))
(assert (= (isPrimeLUT factor3) (_ bv1 8)))
(assert (= (isPrimeLUT factor4) (_ bv1 8)))
(assert (= (isPrimeLUT factor5) (_ bv1 8)))
(assert (= (isPrimeLUT factor6) (_ bv1 8)))

(assert (= (bvmul factor1 factor2 factor3 factor4 factor5 factor6) (_ bv96 8)))

(check-sat)
(get-model)
