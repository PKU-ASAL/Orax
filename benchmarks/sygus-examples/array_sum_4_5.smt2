;; expected program:: (let ((z Int (+ x1 x2))) (ite (> z 5) z (
;;   	    	      let ((z Int (+ x2 x3))) (ite (> z 5) z (
;;   	    	      let ((z Int (+ x3 x4))) (ite (> z 5) z 0))))))


(set-logic QF_UFBV)
(set-option :produce-models true)

(declare-cbf findSum4 ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) (_ BitVec 32)) 
(declare-const x1 (_ BitVec 32))
(declare-const x2 (_ BitVec 32))
(declare-const x3 (_ BitVec 32))
(declare-const x4 (_ BitVec 32))

(assert (bvult (findSum4 x1 x2 x3 x4) (bvadd x1 x2)))
(assert (or (bvugt (bvadd x2 x3) (_ bv5 32)) (= (findSum4 x1 x2 x3 x4) (bvadd x2 x3))))

(assert
	(or (and (and (bvult (bvadd x1 x2) (_ bv5 32)) (bvult (bvadd x2 x3) (_ bv5 32)))
	    	      (bvugt (bvadd x3 x4) (_ bv5 32)))
		 (= (findSum4 x1 x2 x3 x4) (bvadd x3 x4)))
)
		 
(assert (and (and
		(and (bvult (bvadd x1 x2) (_ bv5 32))
		     (bvult (bvadd x2 x3) (_ bv5 32)))
		 (bvult (bvadd x3 x4) (_ bv5 32)))
	     (= (findSum4 x1 x2 x3 x4) (_ bv0 32)))
)


(check-sat)
(get-model)
(exit)
