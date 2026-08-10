Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test58.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_24_05_37_49_696_4987364.v". Abort.
  Verit_Checker "x2020_07_24_05_37_49_696_4987364.smt_in" "x2020_07_24_05_37_49_696_4987364.smt_inproofnew".
End test58.
