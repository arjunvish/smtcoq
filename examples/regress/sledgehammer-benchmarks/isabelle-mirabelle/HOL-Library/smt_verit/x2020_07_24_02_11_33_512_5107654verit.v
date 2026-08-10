Add Rec LoadPath "../../../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test65.
  Goal True. idtac "". idtac "isabelle-mirabelle/HOL-Library/smt_verit/x2020_07_24_02_11_33_512_5107654verit.v". Abort.
  Verit_Checker "x2020_07_24_02_11_33_512_5107654.smt_in" "x2020_07_24_02_11_33_512_5107654.smt_inproofnew".
End test65.

