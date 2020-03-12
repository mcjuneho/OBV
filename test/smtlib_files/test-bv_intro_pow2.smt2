; COMMAND-LINE: --bv-intro-pow2 --no-check-proofs --no-check-unsat-cores

(set-logic QF_BV)

(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(declare-fun z () (_ BitVec 32))
(assert (= z (bvadd x y)))
(assert (distinct x y))
(assert (and (distinct x (_ bv0 32)) (= (bvand x (bvsub x (_ bv1 32))) (_ bv0 32))))
(assert (and (distinct y (_ bv0 32)) (= (bvand y (bvsub y (_ bv1 32))) (_ bv0 32))))
(assert (and (distinct z (_ bv0 32)) (= (bvand z (bvsub z (_ bv1 32))) (_ bv0 32))))
(check-sat)
(exit)
