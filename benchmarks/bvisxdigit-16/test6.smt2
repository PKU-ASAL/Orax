(set-logic QF_UFBV)
(set-option :produce-models true)


(declare-fun ndx () (_ BitVec 16))
(declare-cbf isxdigit_ ((_ BitVec 16)) (_ BitVec 16))

(declare-fun retval () (_ BitVec 16) )
(declare-fun retval_1 () (_ BitVec 16) )
(declare-fun retval_2 () (_ BitVec 16) )
(declare-fun retval_3 () (_ BitVec 16) )
(declare-fun retval_4 () (_ BitVec 16) )
(declare-fun retval_5 () (_ BitVec 16) )

(assert (= retval (isxdigit_ ndx)))
(assert (= retval_1 (isxdigit_ (bvadd ndx (_ bv1 16)))))
(assert (= retval_2 (isxdigit_ (bvadd ndx (_ bv2 16)))))
(assert (= retval_3 (isxdigit_ (bvadd ndx (_ bv3 16)))))
(assert (= retval_4 (isxdigit_ (bvadd ndx (_ bv4 16)))))
(assert (= retval_5 (isxdigit_ (bvadd ndx (_ bv5 16)))))


(assert

(and  (and  (and  (and  (and  (and  (and  (and  (and  (and  (and  (and
(bvule  ndx (_ bv32767 16)  )
(=  false (= (_ bv0 16)  retval ) ) )
(bvule  (bvadd  (_ bv1 16)  ndx ) (_ bv32767 16)  ) )
(=  true (= (_ bv0 16)  retval_1 ) ) )
(bvule  (bvadd  (_ bv2 16)  ndx ) (_ bv32767 16)  ) )
(=  true (=  (_ bv0 16)  retval_2 ) ) )
(bvule  (bvadd  (_ bv3 16)  ndx ) (_ bv32767 16)  ) )
(=  true (=  (_ bv0 16)  retval_3 ) ) )
(bvule  (bvadd  (_ bv4 16)  ndx ) (_ bv32767 16)  ) )
(=  true (=  (_ bv0 16)  retval_4 ) ) )
(bvule  (bvadd  (_ bv5 16)  ndx ) (_ bv32767 16)  ) )
(=  true (=  (_ bv0 16)  retval_5 ) ) )
(bvule  (bvadd  (_ bv6 16)  ndx ) (_ bv32767 16)  ) ) ) 


(check-sat)
(get-model)
(exit)
