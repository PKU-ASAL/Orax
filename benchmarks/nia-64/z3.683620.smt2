(set-info :smt-lib-version 2.6)
(set-logic QF_UFBV)
(set-info :source |Benchmarks from the paper: "Extending Sledgehammer with SMT Solvers" by Jasmin Blanchette, Sascha Bohme, and Lawrence C. Paulson, CADE 2011.  Translated to SMT2 by Andrew Reynolds and Morgan Deters.|)
(set-info :category "industrial")

(declare-fun f1 () (_ BitVec 64))
(declare-fun f2 () (_ BitVec 64))
(declare-fun f3 () (_ BitVec 64))

(declare-cbf _lt ((_ BitVec 64) (_ BitVec 64)) (_ BitVec 64))
(declare-cbf _mul ((_ BitVec 64) (_ BitVec 64)) (_ BitVec 64))

(assert (= f1 f2))
(assert (= (_ bv0 64) (_lt (bvadd (_mul (_ bv4 64) f3) (_ bv1 64)) (_ bv2 64))))
(assert (let ((?v_0 (bvadd (_mul (_ bv4 64) f3) (_ bv1 64)))) (let ((?v_1 (_mul ?v_0 (bvsub ?v_0 (_ bv1 64))))) (= (_ bv1 64) (_lt ?v_1 (bvadd (bvsub ?v_1 ?v_0) (_ bv2 64)))))))
(assert (let ((?v_0 (bvadd (_mul (_ bv4 64) f3) (_ bv1 64)))) (let ((?v_1 (_mul ?v_0 (bvsub ?v_0 (_ bv1 64))))) (= (_ bv1 64) (_lt ?v_1 (bvadd (bvsub ?v_1 ?v_0) (_ bv2 64)))))))

(check-sat)
(exit)
