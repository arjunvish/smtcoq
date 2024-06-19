Add Rec LoadPath "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test1.
  Goal True. idtac "". idtac "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks/individualTests/02andproj/x2020_07_23_15_39_12_904_5134392cvc5.v". Abort.
  Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/individualTests/02cvc5AndProj/x2020_07_23_15_39_12_904_5134392.smt_in" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/individualTests/02cvc5AndProj/x2020_07_23_15_39_12_904_5134392.cvc5pf".
End test1.

