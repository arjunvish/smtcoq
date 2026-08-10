Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test47.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_24_05_38_10_024_5021652verit.v". Abort.
  Verit_Checker "x2020_07_24_05_38_10_024_5021652.smt_in" "x2020_07_24_05_38_10_024_5021652.smt_inproofnew".
End test47.

