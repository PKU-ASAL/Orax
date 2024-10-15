;https://connect.collins.co.uk/repo1/Content/Live/JI/Leckie/GCSE-Maths-Student-Book-Edexcel-Final-03-MarSAMPLEBOOK/wrapper/index.html?r=t#23

(set-logic QF_UFBV)
(set-option :produce-models true)


;  an odd triangular number that is a multiple of 9
(declare-fun isTriangular ((_ BitVec 16) ) (_ BitVec 8))
(declare-fun n () (_ BitVec 16))

(assert (or (= n (_ bv12 16))(= n (_ bv8 16))(= n (_ bv13 16)) (= n (_ bv17 16)) (= n (_ bv15 16)) (= n (_ bv21 16))
	    (= n (_ bv9 16))(= n (_ bv10 16))(= n (_ bv18 16))(= n (_ bv14 16))(= n (_ bv16 16))(= n (_ bv6 16))
	    (= n (_ bv78 16))(= n (_ bv153 16))(= n (_ bv276 16))(= n (_ bv55 16))
	    ))


(declare-fun m () (_ BitVec 16))

(assert (= (bvsmod n (_ bv2 16)) (_ bv1 16)))
(assert (= (isTriangular n) (_ bv1 8)))
(assert (= (bvmul m (_ bv9 16)) n))


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