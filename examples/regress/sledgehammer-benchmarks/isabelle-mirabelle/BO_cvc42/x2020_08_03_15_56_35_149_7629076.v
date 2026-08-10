Add Rec LoadPath "../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test7.
  Goal True. idtac "". idtac "isabelle-mirabelle/BO_cvc42/x2020_08_03_15_56_35_149_7629076.v". Abort.
  Verit_Checker "x2020_08_03_15_56_35_149_7629076.smt_in" "x2020_08_03_15_56_35_149_7629076.smt_inproofnew".
End test7.
