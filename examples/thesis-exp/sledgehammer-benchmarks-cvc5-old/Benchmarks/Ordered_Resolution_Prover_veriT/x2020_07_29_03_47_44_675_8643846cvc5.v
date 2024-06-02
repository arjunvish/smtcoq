Add Rec LoadPath "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test109.
  Goal True. idtac "". idtac "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-cvc5-old/Benchmarks/Ordered_Resolution_Prover_veriT/x2020_07_29_03_47_44_675_8643846cvc5.v". Abort.
  Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-cvc5-old/Benchmarks/Ordered_Resolution_Prover_veriT/x2020_07_29_03_47_44_675_8643846.smt_in" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-cvc5-old/Benchmarks/Ordered_Resolution_Prover_veriT/x2020_07_29_03_47_44_675_8643846.cvc5oldpf".
End test109.

