(set-logic QF_UFBV)

(set-option :produce-models true)

(declare-const c (_ BitVec 8))
(declare-const c1 (_ BitVec 8))
(declare-const c2 (_ BitVec 8))
(declare-const c3 (_ BitVec 8))
(declare-const c4 (_ BitVec 8))

(declare-cbf cbf_tolower ((_ BitVec 8)) (_ BitVec 8))

(declare-fun chr_ret () (_ BitVec 8))
(declare-fun chr_ret_1 () (_ BitVec 8))
(declare-fun chr_ret_2 () (_ BitVec 8))
(declare-fun chr_ret_3 () (_ BitVec 8))
(declare-fun chr_ret_4 () (_ BitVec 8))

(assert (= (cbf_tolower c) chr_ret))
(assert (= (cbf_tolower c1) chr_ret_1))
(assert (= (cbf_tolower c2) chr_ret_2))
(assert (= (cbf_tolower c3) chr_ret_3))
(assert (= (cbf_tolower c4) chr_ret_4))


(assert (and  (and  (and  (and

(= false (= (_ bv97 8) chr_ret))

(=  false (=  (_ bv112 8) chr_ret_1 ) ) )

(=  false (=  (_ bv112 8) chr_ret_2 ) ) )

(=  false (=  (_ bv108 8) chr_ret_3 ) ) )

(=  (_ bv101 8) chr_ret_4 ) ) ) 

(check-sat)
(get-model)
(exit)
