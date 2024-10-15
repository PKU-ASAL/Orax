(set-logic QF_UFBV)

(set-option :produce-models true)

(declare-fun buffer_0_3 () (_ BitVec 64) )
(declare-fun buffer_4_7 () (_ BitVec 64) )
(declare-fun buffer_8_11 () (_ BitVec 64) )
(declare-fun buffer_12_15 () (_ BitVec 64) )
(declare-fun buffer_16_19 () (_ BitVec 64) )
(declare-fun buffer_20_23 () (_ BitVec 64) )

(declare-fun isalpha_ret () (_ BitVec 64) )
(declare-fun isalpha_ret_1 () (_ BitVec 64) )
(declare-fun isalpha_ret_2 () (_ BitVec 64) )
(declare-fun isalpha_ret_3 () (_ BitVec 64) )
(declare-fun isalpha_ret_4 () (_ BitVec 64) )
(declare-fun isalpha_ret_5 () (_ BitVec 64) )

(declare-cbf isalpha_ ((_ BitVec 64)) (_ BitVec 64))

(assert (= isalpha_ret (isalpha_ buffer_0_3)))
(assert (= isalpha_ret_1 (isalpha_ buffer_4_7)))
(assert (= isalpha_ret_2 (isalpha_ buffer_8_11)))
(assert (= isalpha_ret_3 (isalpha_ buffer_12_15)))
(assert (= isalpha_ret_4 (isalpha_ buffer_16_19)))
(assert (= isalpha_ret_5 (isalpha_ buffer_20_23)))

(assert (and  (and  (and  (and  (and  (and  (and (and ( and

(=  false (=  (_ bv0 64) buffer_0_3 ) )

(=  (_ bv0 64) isalpha_ret ) )

(=  false (= (_ bv0 64) buffer_4_7 ) ) )

(=  true (= (_ bv0 64) isalpha_ret_1 ) ) )

(=  false (= (_ bv0 64) buffer_8_11 ) ) )

(=  false (=  (_ bv0 64) isalpha_ret_2 ) ) )

(=  true (=  (_ bv0 64) buffer_12_15 ) ) )

(=  (_ bv0 64) isalpha_ret_3 ) )

(=  false (=  (_ bv0 64) buffer_16_19 ) ) 

(=  (_ bv0 64) isalpha_ret_4 ) )

(=  false (=  (_ bv0 64) buffer_20_23 ) ) 

(=  (_ bv0 64) isalpha_ret_5 ) )

)

(check-sat)
(get-model)
(exit)
