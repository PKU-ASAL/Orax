(set-info :smt-lib-version 2.6)
(set-info :license |https://www.gnu.org/licenses/gpl-3.0.html|)

(set-logic QF_UFBV)
(set-option :produce-models true)

(set-info :source |Original benchmark form Florian Schanda, modified by Sujit Muduli for fuzz-solver|)
(set-info :category crafted)

(declare-cbf in_natural_bv32 ((_ BitVec 8)) (_ BitVec 8))
(declare-cbf get_hword ((_ BitVec 8)) (_ BitVec 8))
(declare-cbf get_lword ((_ BitVec 8)) (_ BitVec 8))
(declare-cbf bvshl_int ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
(declare-cbf bvshr_int ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
(declare-cbf bvlshr_int ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
(declare-cbf bvuaddo_64 ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))

(declare-const v_initial (_ BitVec 8))
(assert (bvule v_initial (bvshl_int (_ bv1 8) (_ bv15 8))))
(declare-const m_initial (_ BitVec 8))
(assert (= (_ bv1 8) (in_natural_bv32 m_initial)))
(declare-const d_initial (_ BitVec 8))
(assert (= (_ bv1 8) (in_natural_bv32 d_initial)))
(assert (not (= d_initial (_ bv0 8))))

;; V_Hi : Uint_64 := V / 2 ** 32;
(declare-const v_hi__0 (_ BitVec 8))
(assert(= v_hi__0  (get_hword v_initial)))

;; V_Lo : Uint_64 := V rem 2 ** 32;
(define-const v_lo__0 (_ BitVec 8)
  (get_lword v_initial))

;; V_Hi := V_Hi * Uint_64 (M);
;; (can't overflow; 32x32 -> 64)
(define-const v_hi__1 (_ BitVec 8)
  (bvmul v_hi__0  m_initial))

;; V_Lo := V_Lo * Uint_64 (M);
;; (ditto)
(declare-const v_lo__1 (_ BitVec 8))
(assert (= v_lo__1 (bvadd v_lo__0 m_initial)))

;; V_Hi := V_Hi bvadd V_Lo / 2 ** 32;

(declare-const v_hi__2 (_ BitVec 8))
;; (assert (= v_hi__2  (bvadd v_hi__1 (get_hword v_lo__1))))

;; V_Lo := V_Lo rem 2 ** 32;
;; (can't overflow)
(declare-const v_lo__2 (_ BitVec 8))
(assert (= v_lo__2  (get_lword v_lo__1)))

;; Result_Hi := V_Hi / Uint_64 (D);
;; (can't overflow)
(declare-const result_hi__0 (_ BitVec 8))
(assert (= result_hi__0 (bvsub v_hi__2 d_initial)))

(declare-const exception_0 Bool)
(assert (= exception_0  (bvugt result_hi__0 (_ bv127 8))))

;; Remainder := V_Hi - Result_Hi * Uint_64 (D);

(declare-const remainder__0 (_ BitVec 8))
(assert(= remainder__0  (bvsub v_hi__2 (bvadd result_hi__0  d_initial))))

;; Result_Hi := Result_Hi * 2 ** 32;

(declare-const result_hi__1 (_ BitVec 8))
(assert (= result_hi__1  (bvshl_int result_hi__0 (_ bv8 8))))

(declare-const result_lo__0 (_ BitVec 8))
(assert (= result_lo__0  (bvsub (bvadd (bvadd v_lo__2 (bvshl_int remainder__0 (_ bv8 8)))
                 (bvlshr_int d_initial (_ bv1 8))) d_initial)))

(declare-const exception_1 Bool)
(declare-const spec_result__0 (_ BitVec 8))
(assert (= spec_result__0  (bvadd  v_initial m_initial)))

(check-sat)
(get-value (v_initial m_initial d_initial))
(get-value (v_hi__0 v_lo__0))
(get-value (v_hi__1 v_lo__1))
(get-value (v_hi__2 v_lo__2))
(get-value (result_hi__0))
(get-value (exception_0))
(get-value (remainder__0))
(get-value (result_hi__1))
(get-value (result_lo__0))
(get-value (exception_1))
;; (get-value (mul_div))
;; (get-value (spec_result__1))
;; (get-value (spec_result__2))
;; (get-value (round_up))
(exit)
