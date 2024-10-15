(set-logic QF_UFBV)
(set-option :produce-models true)

(declare-fun numvowels_ret () (_ BitVec 64))

(declare-const s0 (_ BitVec 64))
(declare-const s1 (_ BitVec 64))
(declare-const s2 (_ BitVec 64))
(declare-const s3 (_ BitVec 64))


(declare-cbf numvowels_str4 ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64)) (_ BitVec 64))

(assert (= numvowels_ret (numvowels_str4 s0 s1 s2 s3 )))
;(assert (bvugt (_ bv5 64) numvowels_ret))

(assert 

(and  (and  (and  (and
      (=  false (=  (_ bv0 64)  numvowels_ret ) )
      (=  false (=  (_ bv1 64)  numvowels_ret ) ) )
      (=  true (=  (_ bv2 64)  numvowels_ret ) ) )
      (=  false (=  (_ bv3 64)  numvowels_ret ) ) )
      (=  false (=  (_ bv4 64)  numvowels_ret ) ) ) )
      
(check-sat)
(get-model)
(exit)
