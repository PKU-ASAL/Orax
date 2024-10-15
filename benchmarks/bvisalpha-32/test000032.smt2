(set-logic QF_UFBV)

(set-option :produce-models true)

(declare-fun buffer_0_3 () (_ BitVec 32) )
(declare-fun buffer_4_7 () (_ BitVec 32) )
(declare-fun buffer_8_11 () (_ BitVec 32) )
(declare-fun buffer_12_15 () (_ BitVec 32) )
(declare-fun buffer_16_19 () (_ BitVec 32) )

(declare-fun isalpha_ret () (_ BitVec 32) )
(declare-fun isalpha_ret_1 () (_ BitVec 32) )
(declare-fun isalpha_ret_2 () (_ BitVec 32) )
(declare-fun isalpha_ret_3 () (_ BitVec 32) )
(declare-fun isalpha_ret_4 () (_ BitVec 32) )

(declare-cbf isalpha ((_ BitVec 32)) (_ BitVec 32))

(assert (= isalpha_ret (isalpha buffer_0_3)))
(assert (= isalpha_ret_1 (isalpha buffer_4_7)))
(assert (= isalpha_ret_2 (isalpha buffer_8_11)))
(assert (= isalpha_ret_3 (isalpha buffer_12_15)))
(assert (= isalpha_ret_4 (isalpha buffer_16_19)))

(assert (and  (and  (and  (and  (and  (and  (and (and

(=  false (=  (_ bv0 32) buffer_0_3 ) )

(=  (_ bv0 32) isalpha_ret ) )

(=  false (= (_ bv0 32) buffer_4_7 ) ) )

(=  false (= (_ bv0 32) isalpha_ret_1 ) ) )

(=  false (= (_ bv0 32) buffer_8_11 ) ) )

(=  false (=  (_ bv0 32) isalpha_ret_2 ) ) )

(=  false (=  (_ bv0 32) buffer_12_15 ) ) )

(=  (_ bv0 32) isalpha_ret_3 ) )

(=  false (=  (_ bv0 32) buffer_16_19 ) ) 

(=  (_ bv0 32) isalpha_ret_4 ) )

)

(check-sat)
(get-model)
(exit)
