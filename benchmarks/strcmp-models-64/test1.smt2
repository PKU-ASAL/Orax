(set-logic QF_UFBV)
(set-option :produce-models true)

(declare-fun retval () (_ BitVec 64))

(declare-const s0 (_ BitVec 64))
(declare-const s1 (_ BitVec 64))
(declare-const s2 (_ BitVec 64))
(declare-const s3 (_ BitVec 64))

(declare-const t0 (_ BitVec 64))
(declare-const t1 (_ BitVec 64))
(declare-const t2 (_ BitVec 64))
(declare-const t3 (_ BitVec 64))


(declare-cbf strcmp_int ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64)
	     		   (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64)) (_ BitVec 64))



(assert  (bvugt s0  (_ bv0 64)))
(assert  (bvugt s1  (_ bv0 64)))
(assert  (bvugt s2  (_ bv0 64)))
(assert  (bvugt s3  (_ bv0 64)))


(assert (= retval (strcmp_int s0 s1 s2 s3 t0 t1 t2 t3)))
(assert (or (= retval (_ bv0 64)) (= retval (_ bv1 64)) (= retval (_ bv2 64))
	    (= retval (_ bv3 64)) (= retval (_ bv4 64))))


(assert (bvuge retval (_ bv3 64) ))

      
(check-sat)
(get-model)
(exit)
