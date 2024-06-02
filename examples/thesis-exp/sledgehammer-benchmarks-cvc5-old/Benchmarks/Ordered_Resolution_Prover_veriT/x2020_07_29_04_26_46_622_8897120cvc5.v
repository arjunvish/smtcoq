Add Rec LoadPath "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test118.
  Goal True. idtac "". idtac "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-cvc5-old/Benchmarks/Ordered_Resolution_Prover_veriT/x2020_07_29_04_26_46_622_8897120cvc5.v". Abort.
  Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-cvc5-old/Benchmarks/Ordered_Resolution_Prover_veriT/x2020_07_29_04_26_46_622_8897120.smt_in" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-cvc5-old/Benchmarks/Ordered_Resolution_Prover_veriT/x2020_07_29_04_26_46_622_8897120.cvc5oldpf".
End test118.

