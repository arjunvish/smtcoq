Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test59.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_24_05_37_49_050_4985034.v". Abort.
  Verit_Checker "x2020_07_24_05_37_49_050_4985034.smt_in" "x2020_07_24_05_37_49_050_4985034.smt_inproofnew".
End test59.
