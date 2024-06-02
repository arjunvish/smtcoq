Add Rec LoadPath "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test4.
  Goal True. idtac "". idtac "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-cvc5-old/Benchmarks/isabelle-mirabelle/BO_cvc42/x2020_08_03_16_50_04_968_5248672cvc5.v". Abort.
  Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-cvc5-old/Benchmarks/isabelle-mirabelle/BO_cvc42/x2020_08_03_16_50_04_968_5248672.smt_in" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-cvc5-old/Benchmarks/isabelle-mirabelle/BO_cvc42/x2020_08_03_16_50_04_968_5248672.cvc5oldpf".
End test4.

