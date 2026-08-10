Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test10.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_17_06_27_504_5933684verit.v". Abort.
  Verit_Checker "x2020_08_03_17_06_27_504_5933684.smt_in" "x2020_08_03_17_06_27_504_5933684.smt_inproofnew".
End test10.

