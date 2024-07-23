(set-logic UFLIA)
(declare-sort Tindex_0 0)
(declare-sort Tindex_1 0)
(declare-sort Tindex_2 0)
(declare-fun op_3 (Tindex_0 Tindex_2) Tindex_0)
(declare-fun op_2 () Tindex_2)
(declare-fun op_1 (Tindex_1) Tindex_0)
(declare-fun op_0 (Tindex_1) Tindex_0)
(assert (not (= (op_3 op_0 op_2) (op_3 op_1 op_2))))
(assert (forall ( (SMTCoqRelName7 Tindex_1) ) (= (op_0 SMTCoqRelName7) (op_1 SMTCoqRelName7))))
(check-sat)
(exit)
