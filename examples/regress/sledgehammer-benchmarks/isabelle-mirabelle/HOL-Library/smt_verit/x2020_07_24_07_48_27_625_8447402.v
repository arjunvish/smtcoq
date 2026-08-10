Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test50.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_24_07_48_27_625_8447402.v". Abort.
  Verit_Checker "x2020_07_24_07_48_27_625_8447402.smt_in" "x2020_07_24_07_48_27_625_8447402.smt_inproofnew".
End test50.
