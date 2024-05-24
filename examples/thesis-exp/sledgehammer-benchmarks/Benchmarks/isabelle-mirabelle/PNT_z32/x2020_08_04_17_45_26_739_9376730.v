Add Rec LoadPath "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.


Section test1.
  Goal True. idtac "". idtac "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-norulesnoexists/Benchmarks/isabelle-mirabelle/PNT_z32/x2020_08_04_17_45_26_739_9376730.smt_in". Abort.
  Verit_Checker "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-norulesnoexists/Benchmarks/isabelle-mirabelle/PNT_z32/x2020_08_04_17_45_26_739_9376730.smt_in" "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/thesis-exp/sledgehammer-benchmarks-norulesnoexists/Benchmarks/isabelle-mirabelle/PNT_z32/x2020_08_04_17_45_26_739_9376730.smt_inproofnew".
End test1.
