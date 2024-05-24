Add Rec LoadPath "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test71.
  Goal True. idtac "". idtac "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-norulesnoexists/Benchmarks/isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_24_08_38_00_870_5908880.smt_in". Abort.
  Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-norulesnoexists/Benchmarks/isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_24_08_38_00_870_5908880.smt_in" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-norulesnoexists/Benchmarks/isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_24_08_38_00_870_5908880.smt_inproofnew".
End test71.
