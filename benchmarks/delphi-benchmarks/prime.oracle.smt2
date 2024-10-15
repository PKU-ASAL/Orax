(set-logic QF_UFBV)

(declare-fun isPrimeLUT ((_ BitVec 32) ) (_ BitVec 8))

; note that this will only say "unsat" or "unknown", should do unsat queries below


; Example:
; 769129 = 877 * 877 ... slow ~5 seconds

(assert (= (isPrimeLUT (_ bv242 32)) (_ bv1 8)))

(check-sat)