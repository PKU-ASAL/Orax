
(set-info :license |https://www.gnu.org/licenses/gpl-3.0.html|)

(set-logic QF_UFBV)
(set-option :produce-models true)

(declare-const r1 (_ BitVec 8))
(declare-const r2 (_ BitVec 8))
(declare-const r3 (_ BitVec 8))

(declare-cbf cbf_bvrem ((_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))

(define-const m (_ BitVec 8) (_ bv120 8))

(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))

;; we have a type mod m

(assert (bvult x m))
(assert (bvult y m))

;; (x + y) mod 250  <without casting>
(assert (= r3 (bvadd x y)))
(assert (= r1  (cbf_bvrem r3 m) ) )

;; (x + y) mod 250  <with casting>
(assert (= r2 (cbf_bvrem (bvsub x y) m)))

(assert (not (= r1 r2)))

(check-sat)
(get-value (x y))
(get-value (r1 r2))
(exit)
