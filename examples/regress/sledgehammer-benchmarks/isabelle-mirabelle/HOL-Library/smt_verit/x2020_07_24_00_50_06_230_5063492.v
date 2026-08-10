Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test34.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_24_00_50_06_230_5063492.v". Abort.
  Verit_Checker "x2020_07_24_00_50_06_230_5063492.smt_in" "x2020_07_24_00_50_06_230_5063492.smt_inproofnew".
End test34.
