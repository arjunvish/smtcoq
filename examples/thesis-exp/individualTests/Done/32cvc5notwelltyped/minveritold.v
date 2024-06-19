Add Rec LoadPath "/home/arjun/Desktop/smtcoq/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test23.
  Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/individualTests/32cvc5/min.smt2" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/individualTests/32cvc5/min2.verit2016pf".
End test23.

