Add Rec LoadPath "/home/sagar/Desktop/smtcoq/arjunvish-alethe_coq8.13/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.
Section Benchmark.
  Verit_Checker "/home/sagar/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test1/test1.smt2" "/home/sagar/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test1/test1-unshared.veritpf".
End Benchmark.
