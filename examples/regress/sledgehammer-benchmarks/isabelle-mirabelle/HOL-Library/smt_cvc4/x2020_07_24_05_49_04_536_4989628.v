Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test75.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_24_05_49_04_536_4989628.v". Abort.
  Verit_Checker "x2020_07_24_05_49_04_536_4989628.smt_in" "x2020_07_24_05_49_04_536_4989628.smt_inproofnew".
End test75.
