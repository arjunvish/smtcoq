Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test68.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_24_09_13_25_289_5134680.v". Abort.
  Verit_Checker "x2020_07_24_09_13_25_289_5134680.smt_in" "x2020_07_24_09_13_25_289_5134680.smt_inproofnew".
End test68.
