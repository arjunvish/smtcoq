Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test37.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_23_17_45_18_358_5383148verit.v". Abort.
  Verit_Checker "x2020_07_23_17_45_18_358_5383148.smt_in" "x2020_07_23_17_45_18_358_5383148.smt_inproofnew".
End test37.

