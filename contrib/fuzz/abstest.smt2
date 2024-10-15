(set-logic QF_UFLIA)
(set-option :produce-models true)

(declare-fun absx (Int) Int)
(declare-const x Int)
(declare-const y Int)

(assert (= (absx x) 1))
(assert (= (absx y) (absx x)))

(assert (> x 0))

(check-sat)
(get-model)