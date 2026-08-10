Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test55.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_23_19_06_15_118_5385958verit.v". Abort.
  Verit_Checker "x2020_07_23_19_06_15_118_5385958.smt_in" "x2020_07_23_19_06_15_118_5385958.smt_inproofnew".
End test55.

