;https://connect.collins.co.uk/repo1/Content/Live/JI/Leckie/GCSE-Maths-Student-Book-Edexcel-Final-03-MarSAMPLEBOOK/wrapper/index.html?r=t#23

(set-logic QF_UFBV)
(set-option :produce-models true)

;  an odd triangular number that is a multiple of 7
(declare-fun isTriangular ((_ BitVec 8) ) (_ BitVec 8))


(declare-fun n () (_ BitVec 8))
(assert (or (= n (_ bv12 8))(= n (_ bv8 8))(= n (_ bv13 8)) (= n (_ bv17 8)) (= n (_ bv15 8)) (= n (_ bv21 8))
	    (= n (_ bv9 8))(= n (_ bv10 8))(= n (_ bv18 8))(= n (_ bv14 8))(= n (_ bv16 8))(= n (_ bv6 8)) ))

(declare-fun m () (_ BitVec 8))

(assert (= (bvsmod n (_ bv2 8)) (_ bv1 8)))
(assert (= (isTriangular n) (_ bv1 8)))
(assert (= (bvmul m (_ bv7 8)) n))


(check-sat)
(get-model)

; a. a multiple of 3 and a multiple of 4
; b. a square number and an odd number
; c. a factor of 24 and a factor of 18
; d. a prime number and a factor of 39
; e. an odd factor of 30 and a multiple of 3
; f. a number with four factors and a multiple of 2 and 7
; g. a number with five factors exactly
; h. a triangular number and a factor of 20
; i. an even number and a factor of 36 and a multiple of 9
; j. a prime number that is one more than a square number
; k. a number with factors that, when written out in order, make a number pattern in which each number is twice the one before
; l. an odd triangular number that is a multiple of 7