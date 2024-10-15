(set-logic QF_UFBV)

(set-option :produce-models true)

(declare-fun buffer_0_3 () (_ BitVec 16) )
(declare-fun buffer_4_7 () (_ BitVec 16) )
(declare-fun buffer_8_11 () (_ BitVec 16) )
(declare-fun buffer_12_15 () (_ BitVec 16) )
(declare-fun buffer_16_19 () (_ BitVec 16) )
(declare-fun buffer_20_23 () (_ BitVec 16) )
(declare-fun buffer_23_26 () (_ BitVec 16) )
(declare-fun buffer_7 () (_ BitVec 16) )
(declare-fun buffer_8 () (_ BitVec 16) )
(declare-fun buffer_9 () (_ BitVec 16) )
(declare-fun buffer_10 () (_ BitVec 16) )

(declare-fun isalpha_ret () (_ BitVec 16) )
(declare-fun isalpha_ret_1 () (_ BitVec 16) )
(declare-fun isalpha_ret_2 () (_ BitVec 16) )
(declare-fun isalpha_ret_3 () (_ BitVec 16) )
(declare-fun isalpha_ret_4 () (_ BitVec 16) )
(declare-fun isalpha_ret_5 () (_ BitVec 16) )
(declare-fun isalpha_ret_6 () (_ BitVec 16) )
(declare-fun isalpha_ret_7 () (_ BitVec 16) )
(declare-fun isalpha_ret_8 () (_ BitVec 16) )
(declare-fun isalpha_ret_9 () (_ BitVec 16) )
(declare-fun isalpha_ret_10 () (_ BitVec 16) )

(declare-cbf isalpha ((_ BitVec 16)) (_ BitVec 16))

(assert (= isalpha_ret (isalpha buffer_0_3)))
(assert (= isalpha_ret_1 (isalpha buffer_4_7)))
(assert (= isalpha_ret_2 (isalpha buffer_8_11)))
(assert (= isalpha_ret_3 (isalpha buffer_12_15)))
(assert (= isalpha_ret_4 (isalpha buffer_16_19)))
(assert (= isalpha_ret_5 (isalpha buffer_20_23)))
(assert (= isalpha_ret_6 (isalpha buffer_23_26)))
(assert (= isalpha_ret_7 (isalpha buffer_7)))
(assert (= isalpha_ret_8 (isalpha buffer_8)))
(assert (= isalpha_ret_9 (isalpha buffer_9)))
(assert (= isalpha_ret_10 (isalpha buffer_10)))

(assert (and  (and  (and  (and  (and  (and  (and (and ( and ( and ( and ( and ( and ( and 

(=  false (=  (_ bv0 16) buffer_0_3 ) )

(=  (_ bv0 16) isalpha_ret ) )

(=  false (= (_ bv0 16) buffer_4_7 ) ) )

(=  true (= (_ bv0 16) isalpha_ret_1 ) ) )

(=  false (= (_ bv0 16) buffer_8_11 ) ) )

(=  true (=  (_ bv0 16) isalpha_ret_2 ) ) )

(=  false (=  (_ bv0 16) buffer_12_15 ) ) )

(= true (=  (_ bv0 16) isalpha_ret_3 ) ) )

(=  false (=  (_ bv0 16) buffer_16_19 ) ) 

(=  (_ bv0 16) isalpha_ret_4 ) )

(=  false (=  (_ bv0 16) buffer_20_23 ) ) 

(=  (_ bv0 16) isalpha_ret_5 ) )

(=  false (=  (_ bv0 16) buffer_23_26 ) ) 

(=  (_ bv0 16) isalpha_ret_6 ) )

(=  false (=  (_ bv0 16) buffer_7 ) ) 
(=  true (= (_ bv0 16) isalpha_ret_7 ) ) )

(=  false (=  (_ bv0 16) buffer_8 ) ) 
(=  true (= (_ bv0 16) isalpha_ret_8 ) ) )

(=  false (=  (_ bv0 16) buffer_9 ) ) 
(=  true (= (_ bv0 16) isalpha_ret_9 ) ) )

(=  false (=  (_ bv0 16) buffer_10 ) ) 
(=  false (= (_ bv0 16) isalpha_ret_10 ) ) )

)

(check-sat)
(get-model)
(exit)
