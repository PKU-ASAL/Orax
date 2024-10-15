(set-logic QF_UFBV)
(set-option :produce-models true)

(declare-cbf isxdigit_ ((_ BitVec 64)) (_ BitVec 64))
(declare-fun ndx () (_ BitVec 64))
(declare-fun retval () (_ BitVec 64))

(assert (= retval (isxdigit_ ndx)))

(assert
     (and
	 (and
		(bvule ndx (_ bv32767 64) )
		(=  (_ bv0 64)  retval ))
	
	 (=  false (bvule  (bvadd  (_ bv1 64) ndx ) (_ bv32767 64) ) ) )
)

(check-sat)
(get-model)
(exit)
