Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test85.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_24_08_38_08_504_5931826verit.v". Abort.
  Verit_Checker "x2020_07_24_08_38_08_504_5931826.smt_in" "x2020_07_24_08_38_08_504_5931826.smt_inproofnew".
End test85.

