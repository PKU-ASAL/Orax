(set-logic QF_UFBV)
(set-option :produce-models true)

(declare-fun retval () (_ BitVec 32))

(declare-const s0 (_ BitVec 32))
(declare-const s1 (_ BitVec 32))
(declare-const s2 (_ BitVec 32))
(declare-const s3 (_ BitVec 32))

(declare-const t0 (_ BitVec 32))
(declare-const t1 (_ BitVec 32))
(declare-const t2 (_ BitVec 32))
(declare-const t3 (_ BitVec 32))


(declare-cbf strcmp_int ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32)
	     		   (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))


(assert  (= s0  (_ bv1 32)))
(assert  (= s1  (_ bv1 32)))
(assert  (= s2  (_ bv1 32)))
(assert  (= s3  (_ bv1 32)))
(assert  (= t0  (_ bv1 32)))


(assert (= retval (strcmp_int s0 s1 s2 s3 t0 t1 t2 t3)))
(assert (= retval (_ bv3 32)))

(assert (bvugt (_ bv5 32) retval))

      
(check-sat)

(exit)
