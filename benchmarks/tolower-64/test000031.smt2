(set-logic QF_UFBV)

(set-option :produce-models true)

(declare-const c (_ BitVec 64))
(declare-const c1 (_ BitVec 64))
(declare-const c2 (_ BitVec 64))
(declare-const c3 (_ BitVec 64))
(declare-const c4 (_ BitVec 64))

(declare-cbf cbf_tolower ((_ BitVec 64)) (_ BitVec 64))

(declare-fun chr_ret () (_ BitVec 64))
(declare-fun chr_ret_1 () (_ BitVec 64))
(declare-fun chr_ret_2 () (_ BitVec 64))
(declare-fun chr_ret_3 () (_ BitVec 64))
(declare-fun chr_ret_4 () (_ BitVec 64))

(assert (= (cbf_tolower c) chr_ret))
(assert (= (cbf_tolower c1) chr_ret_1))
(assert (= (cbf_tolower c2) chr_ret_2))
(assert (= (cbf_tolower c3) chr_ret_3))
(assert (= (cbf_tolower c4) chr_ret_4))

(assert (and  (and  (and  (and
	(=  (_ bv97 64) chr_ret )
	(=  (_ bv112 64) chr_ret_1 ) )
	(=  (_ bv112 64) chr_ret_2 ) )
	(=  (_ bv112 64) chr_ret_3 ) )
	(=  (_ bv101 64) chr_ret_4 ) )
)

(check-sat)

(exit)
