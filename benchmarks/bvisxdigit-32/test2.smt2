(set-logic QF_UFBV)
(set-option :produce-models true)
(set-option :simplification none)

(declare-cbf isxdigit_ ((_ BitVec 32)) (_ BitVec 32))
(declare-fun ndx () (_ BitVec 32) )

(declare-fun retval () (_ BitVec 32))
(declare-fun retval_1 () (_ BitVec 32))
(declare-fun retval_2 () (_ BitVec 32))

(assert (= retval (isxdigit_ ndx)))
(assert (= retval_1 (isxdigit_ (bvadd ndx (_ bv1 32)))))
(assert (= retval_2 (isxdigit_ (bvadd ndx (_ bv2 32)))))


(assert
  (and
    (and
      (and
        (and
          (and
	    (and
	      (bvule ndx (_ bv32767 32) )
	      (=  (_ bv0 32) retval ) )
	    (bvule (bvadd (_ bv1 32) ndx) (_ bv32767 32) ))
	    (=  (_ bv0 32) retval_1 ))

	(bvule  (bvadd (_ bv2 32) ndx) (_ bv32767 32) ))
	(=  (_ bv0 32) retval_2 ))
   (=  false (bvule  (bvadd (_ bv3 32) ndx ) (_ bv32767 32) ))
 ))


(check-sat)
(get-model)
(exit)
