Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test41.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_24_00_32_10_259_5099720verit.v". Abort.
  Verit_Checker "x2020_07_24_00_32_10_259_5099720.smt_in" "x2020_07_24_00_32_10_259_5099720.smt_inproofnew".
End test41.

