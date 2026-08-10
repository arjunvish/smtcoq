Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test48.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_24_02_50_00_147_4983028verit.v". Abort.
  Verit_Checker "x2020_07_24_02_50_00_147_4983028.smt_in" "x2020_07_24_02_50_00_147_4983028.smt_inproofnew".
End test48.

