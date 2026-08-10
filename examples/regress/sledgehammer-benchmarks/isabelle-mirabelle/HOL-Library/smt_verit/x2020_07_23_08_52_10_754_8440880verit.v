Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test51.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_23_08_52_10_754_8440880verit.v". Abort.
  Verit_Checker "x2020_07_23_08_52_10_754_8440880.smt_in" "x2020_07_23_08_52_10_754_8440880.smt_inproofnew".
End test51.

