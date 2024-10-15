(set-logic QF_UFLIA)
(set-option :produce-models true)


(declare-fun absx (Int) Int)
(declare-const x Int)
(declare-const y Int)

(assert (= (absx 1) x))
(assert (= (absx y) (absx x)))
;; (assert (= ( - x y) 0))
(assert ( = (+ x y) 2))

(check-sat)
(get-model)