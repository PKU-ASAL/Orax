(set-logic QF_UFBV)
(set-option :produce-models true)
(declare-fun numvowels_ret () (_ BitVec 16))

(declare-const s0 (_ BitVec 16))
(declare-const s1 (_ BitVec 16))
(declare-const s2 (_ BitVec 16))
(declare-const s3 (_ BitVec 16))
(declare-const s4 (_ BitVec 16))
(declare-const s5 (_ BitVec 16))


(declare-cbf numvowels_str6 ((_ BitVec 16) (_ BitVec 16) (_ BitVec 16) (_ BitVec 16) (_ BitVec 16) (_ BitVec 16)) (_ BitVec 16))

(assert (= numvowels_ret (numvowels_str6 s0 s1 s2 s3 s4 s5)))
(assert (bvugt (_ bv6 16) numvowels_ret))

(assert 

(and  (and  (and 
      (=  false (=  (_ bv0 16)  numvowels_ret ) )
      (=  false (=  (_ bv1 16)  numvowels_ret ) ) )
      (=  false (=  (_ bv2 16)  numvowels_ret ) ) )
      (=  true  (=  (_ bv3 16)  numvowels_ret ) ) ) )
      
(check-sat)
(get-model)
(exit)
