(set-logic QF_UFBV)
(set-option :produce-models true)
;; (set-option :simplification none)

(declare-fun icmp ((_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))

(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(declare-const icmp_ret (_ BitVec 32))

(assert (bvsgt (icmp x y) (_ bv0 32))

(check-sat)
(get-model)