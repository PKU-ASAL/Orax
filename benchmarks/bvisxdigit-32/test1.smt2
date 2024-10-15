(set-logic QF_UFBV)
(set-option :produce-models true)

(declare-cbf isxdigit_ ((_ BitVec 32)) (_ BitVec 32))
(declare-fun ndx () (_ BitVec 32))
(declare-fun retval () (_ BitVec 32))

(assert (= retval (isxdigit_ ndx)))

(assert
     (and
	 (and
		(bvule ndx (_ bv32767 32) )
		(=  (_ bv0 32)  retval ))
	
	 (=  false (bvule  (bvadd  (_ bv1 32) ndx ) (_ bv32767 32) ) ) )
)

(check-sat)

(exit)
