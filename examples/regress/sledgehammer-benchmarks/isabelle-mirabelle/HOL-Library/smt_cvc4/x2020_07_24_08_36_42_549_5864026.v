Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test77.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_24_08_36_42_549_5864026.v". Abort.
  Verit_Checker "x2020_07_24_08_36_42_549_5864026.smt_in" "x2020_07_24_08_36_42_549_5864026.smt_inproofnew".
End test77.
