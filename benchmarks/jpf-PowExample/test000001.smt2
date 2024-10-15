(set-logic QF_UFBV)

(set-option :produce-models true)
(set-option :simplification none)

(declare-cbf ipow2 ((_ BitVec 32)) (_ BitVec 32))
(declare-fun ipow2_ret () (_ BitVec 32))
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))

(assert ( = ipow2_ret  (ipow2 x)))
(assert (bvule (_ bv0 32) ipow2_ret))
        
(check-sat)

(exit)
