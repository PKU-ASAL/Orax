(set-logic QF_UFLIA)
(set-option :produce-models true)

(declare-fun absx (Int) Int)

(declare-fun x10 () Int)
(declare-const x34 Int)
(declare-const y Int)
(declare-const tempx Int)

(assert ( = (absx x10) tempx))
(assert ( > tempx 0))
(assert (= x34 (* 2 y)))
(assert (< x10 x34))

(check-sat)
(get-model)