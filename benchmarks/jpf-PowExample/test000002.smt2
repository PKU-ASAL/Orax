(set-logic QF_UFBV)
(set-option :produce-models true)
(set-option :simplification none)

(declare-fun ipow ((_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))
(declare-fun ipow_ret () (_ BitVec 32))
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))

(assert ( = ipow_ret (ipow x (_ bv2 32))))

(assert
        
        (and
             (and
                (bvult  (_ bv0 32) x )
                (=  false (=  y  ipow_ret) )
             )
             (=  false (bvult  (_ bv8 32) y ))
	)
)
        
(check-sat)

(exit)
