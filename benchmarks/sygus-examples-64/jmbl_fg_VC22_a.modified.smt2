(set-logic QF_UFBV)
(set-option :produce-models true)

(declare-cbf f_jmbl_fg_VC22_a ((_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))

(define-const V_min (_ BitVec 32)
    (_ bv1 32))

(define-const V_mux_ (_ BitVec 32)
    (_ bv2 32))

(define-fun Zero ((v (_ BitVec 32))) Bool
    (= v (_ bv0 32)))

(declare-cbf InV1 ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))

(declare-cbf InV2 ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))

(define-fun InVorZero ((v (_ BitVec 32))) Bool
    (or (= (_ bv1 32) (InV1 v V_min V_mux_)) (Zero v)))

(declare-cbf UnsafeSame ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))
;;    (or (and (bvugt x1 x2) (bvugt (bvadd x2 v2) (bvadd x1 v1))) (and (bvugt x2 x1) (bvugt (bvadd x1 v1) (bvadd x2 v2)))))

(define-fun Unsafe ((x1 (_ BitVec 32)) (x2 (_ BitVec 32)) (v1 (_ BitVec 32)) (v2 (_ BitVec 32))) Bool
    (= (_ bv1 32) (UnsafeSame x1 x2 v1 v2)))

(define-fun Mad_Same ((x1 (_ BitVec 32)) (x2 (_ BitVec 32))) Bool
    (= x1 x2))

(define-fun Mad_ ((x1 (_ BitVec 32)) (x2 (_ BitVec 32))) Bool
    (Mad_Same x1 x2))

(declare-const x1 (_ BitVec 32))
(declare-const x2 (_ BitVec 32))
(declare-const v1 (_ BitVec 32))
(declare-const v2 (_ BitVec 32))
(assert ( InVorZero (f_jmbl_fg_VC22_a x1 x2)))

(assert (and (or (= (_ bv1 32) (InV2 v1 v2 V_min V_mux_))
	    	(Zero (f_jmbl_fg_VC22_a x1 x2)))
	    (and
		(Unsafe x1 x2 (f_jmbl_fg_VC22_a x1 x2) (f_jmbl_fg_VC22_a x1 x2))
		(not (Zero (f_jmbl_fg_VC22_a (bvadd x1 (f_jmbl_fg_VC22_a x1 x2)) (bvadd x2 (f_jmbl_fg_VC22_a x1 x2))))))))

(assert (and (or
		(not (= (_ bv1 32) (InV2 v1 v2 V_min V_mux_)))
		     (or (Unsafe x1 x2 v1 v2)
		     	 (Zero (f_jmbl_fg_VC22_a (bvadd x1 v1) (bvadd x2 v2)) ) ))

	    (not (Zero (f_jmbl_fg_VC22_a x1 x2)))))

(assert (or (Mad_ x1 x2) (not (Zero (f_jmbl_fg_VC22_a x1 x2)))))

(check-sat)
(get-model)
(exit)