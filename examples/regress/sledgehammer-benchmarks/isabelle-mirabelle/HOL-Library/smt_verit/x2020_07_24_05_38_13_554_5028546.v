Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test37.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_24_05_38_13_554_5028546.v". Abort.
  Verit_Checker "x2020_07_24_05_38_13_554_5028546.smt_in" "x2020_07_24_05_38_13_554_5028546.smt_inproofnew".
End test37.
