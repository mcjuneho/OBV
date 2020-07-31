(set-logic QF_BV)



(declare-fun v0 () (_ BitVec 16))
(declare-fun v1 () (_ BitVec 16))
(declare-fun v2 () (_ BitVec 16))
(declare-fun v3 () (_ BitVec 16))
(declare-fun v4 () (_ BitVec 16))
(declare-fun v5 () (_ BitVec 16))
(assert (and
	 (bvult v0 v1)
	 (bvult (_ bv5 16) v3)
	 (bvult v1 v2)
	 (bvult v1 v3)
	 (bvult v5 (_ bv8 16))
	 (bvult v2 v4)
	 (bvult v3 v4)
	 (bvult v4 v5)
	 ))
(check-sat)
(exit)
