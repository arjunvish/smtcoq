Add Rec LoadPath "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test2.
  Goal True. idtac "". idtac "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/individualTests/01missingDischargeStep/x2020_08_03_16_40_35_239_4899098cvc5.v". Abort.
  Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/individualTests/01cvc5MissingDischargeStep/x2020_08_03_16_40_35_239_4899098.smt_in" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/individualTests/01cvc5MissingDischargeStep/x2020_08_03_16_40_35_239_4899098.cvc5pf".
End test2.

