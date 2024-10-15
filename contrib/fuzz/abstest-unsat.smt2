(set-logic QF_UFLIA)

(declare-fun absx (Int) Int)
(declare-const x Int)
(declare-const y Int)

(assert (= (absx (absx x)) x))
(assert (= (absx x) y))
(assert (not (= (absx (absx x)) y)))
(check-sat)