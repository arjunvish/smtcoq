Add Rec LoadPath "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test72.
  Goal True. idtac "". idtac "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-cvc5-old/Benchmarks/isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_24_08_33_14_874_5693428cvc5.v". Abort.
  Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-cvc5-old/Benchmarks/isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_24_08_33_14_874_5693428.smt_in" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-cvc5-old/Benchmarks/isabelle-mirabelle/HOL-Library/smt_cvc4/x2020_07_24_08_33_14_874_5693428.cvc5oldpf".
End test72.

