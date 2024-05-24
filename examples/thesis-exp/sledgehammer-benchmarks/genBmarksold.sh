#!/bin/bash
#Go through all the .smt2 files in the directory, add a statement to check the file with its corresponding .smt2.proof file to sledgehammer.v and also create a *.v file that independently checks this file
#Also add a call to coqc on the independent files to a separate script so that they can be called independently.

coqclist="coqclist.sh"
echo "#!/bin/bash" > $coqclist
echo "" >> $coqclist

sledgehammer="sledgehammer.v"
#To sledgehammer.v, add the following lines
echo "Add Rec LoadPath \"/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src\" as SMTCoq." > $sledgehammer
echo "Require Import SMTCoq.SMTCoq." >> $sledgehammer
echo "Require Import Bool." >> $sledgehammer
echo "" >> $sledgehammer
echo "" >> $sledgehammer
ctr=1
for relpathsmt in $(find ./ -name '*.smt_in'); do
  echo "Relative Path: $relpathsmt"
  abspathsmt=$(realpath $relpathsmt)
  echo "Absolute Path: $abspathsmt"
  abspathveritpf=${abspathsmt/\.smt_in/\.smt_inproofnew}
  echo "Absolute Path of Verit Proof File: $abspathveritpf"
  abspathcoq=${abspathsmt/\.smt_in/\.v}
  echo "Absolute Path of Coq File: $abspathcoq"

  #This next commented section would call both solvers to create proofs
  #abspathcvc5pf=${abspathsmt/\.smt2/\.cvc5pf}
  #echo "Absolute Path of cvc5 Proof File: $abspathcvc5pf"
  #barefname=${relpathsmt%\.smt2}
  #echo "Bare File Name: $barefname"
  #veritpfname="$barefname.veritpf"
  #echo "VeriT Proof File Name: $veritpfname"
  #cvc5pfname="$barefname.cvc5pf"
  #echo "cvc5 Proof File Name: $cvc5pfname"
  #timeout 60 cvc5-rare $relpathsmt --dump-proofs --proof-format-mode=alethe --proof-granularity=dsl-rewrite --dag-thresh=0 | tail -n +2 > $cvc5pfname
  #timeout 60 veriT --proof-prune --proof-merge --proof-with-sharing --cnf-definitional --disable-ackermann --input=smtlib2 --proof=$veritpfname $relpathsmt

  #To sledgehammer.v, add
  echo "Section test$ctr." >> $sledgehammer
  echo "  Goal True. idtac \"\". idtac \"$abspathcoq\". Abort." >> $sledgehammer
  echo "  Verit_Checker \"$abspathsmt\" \"$abspathveritpf\"." >> $sledgehammer
  echo "End test$ctr." >> $sledgehammer
  echo "" >> $sledgehammer
  
  echo "Add Rec LoadPath \"/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src\" as SMTCoq." > $abspathcoq
  echo "Require Import SMTCoq.SMTCoq." >> $abspathcoq
  echo "Require Import Bool." >> $abspathcoq
  echo "" >> $abspathcoq
  echo "" >> $abspathcoq
  echo "Section test$ctr." >> $abspathcoq
  echo "  Goal True. idtac \"\". idtac \"$abspathsmt\". Abort." >> $abspathcoq
  echo "  Verit_Checker \"$abspathsmt\" \"$abspathveritpf\"." >> $abspathcoq
  echo "End test$ctr." >> $abspathcoq
  echo "" >> $sledgehammer
  
  echo "coqc $abspathcoq" >> $coqclist
  
  ctr=$((ctr+1))
  echo ""
done;
