Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test38.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_24_07_46_56_736_8400646verit.v". Abort.
  Verit_Checker "x2020_07_24_07_46_56_736_8400646.smt_in" "x2020_07_24_07_46_56_736_8400646.smt_inproofnew".
End test38.

