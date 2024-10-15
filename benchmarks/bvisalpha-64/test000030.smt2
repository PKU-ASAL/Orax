(set-logic QF_UFBV)

(set-option :produce-models true)

(declare-fun buffer_0_3 () (_ BitVec 64) )
(declare-fun buffer_4_7 () (_ BitVec 64) )
(declare-fun buffer_8_11 () (_ BitVec 64) )
(declare-fun buffer_12_15 () (_ BitVec 64) )

(declare-fun isalpha_ret () (_ BitVec 64) )
(declare-fun isalpha_ret_1 () (_ BitVec 64) )
(declare-fun isalpha_ret_2 () (_ BitVec 64) )
(declare-fun isalpha_ret_3 () (_ BitVec 64) )

(declare-cbf isalpha_ ((_ BitVec 64)) (_ BitVec 64))

(assert (= isalpha_ret (isalpha_ buffer_0_3)))
(assert (= isalpha_ret_1 (isalpha_ buffer_4_7)))
(assert (= isalpha_ret_2 (isalpha_ buffer_8_11)))
(assert (= isalpha_ret_3 (isalpha_ buffer_12_15)))

(assert (and  (and  (and  (and  (and  (and  (and

(=  false (=  (_ bv0 64) buffer_0_3 ) )

(=  false ( = (_ bv0 64) isalpha_ret ) ) )

(=  false (= (_ bv0 64) buffer_4_7 ) ) )

(=  true (= (_ bv0 64) isalpha_ret_1 ) ) )

(=  false (= (_ bv0 64) buffer_8_11 ) ) )

(=  true (=  (_ bv0 64) isalpha_ret_2 ) ) )

(=  false (=  (_ bv0 64) buffer_12_15 ) ) )

(=  (_ bv0 64) isalpha_ret_3 ) ) )

(check-sat)
(get-model)
(exit)
