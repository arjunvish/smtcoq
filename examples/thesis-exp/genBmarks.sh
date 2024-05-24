#!/bin/bash
#Go through all the .smt2 files in the directory, add a statement to check the file with its corresponding .smt2.proof file to qfuf.v and also create a *.v file that independently checks this file
#Also add a call to coqc on the independent files to a separate script so that they can be called independently.

coqclist="coqclist.sh"
echo "#!/bin/bash" > $coqclist
echo "" >> $coqclist

qfuf="qfuf.v"
#To qfuf.v, add the following lines
echo "Add Rec LoadPath \"/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src\" as SMTCoq." > $qfuf
echo "Require Import SMTCoq.SMTCoq." >> $qfuf
echo "Require Import Bool." >> $qfuf
echo "" >> $qfuf
echo "" >> $qfuf
ctr=1
for relpathsmt in $(find ./ -name '*.smt2'); do
  echo "Relative Path: $relpathsmt"
  abspathsmt=$(realpath $relpathsmt)
  echo "Absolute Path: $abspathsmt"
  abspathveritpf=${abspathsmt/\.smt2/\.smt2\.proof}
  echo "Absolute Path of Verit Proof File: $abspathveritpf"
  abspathcvc5pf=${abspathsmt/\.smt2/\.cvc5pf}
  echo "Absolute Path of cvc5 Proof File: $abspathcvc5pf"
  abspathcoq=${abspathsmt/\.smt2/\.v}
  echo "Absolute Path of Coq File: $abspathcoq"
  barefname=${relpathsmt%\.smt2}
  echo "Bare File Name: $barefname"
  veritpfname="$barefname.veritpf"
  echo "VeriT Proof File Name: $veritpfname"
  cvc5pfname="$barefname.cvc5pf"
  echo "cvc5 Proof File Name: $cvc5pfname"
  #timeout 60 cvc5-rare $relpathsmt --dump-proofs --proof-format-mode=alethe --proof-granularity=dsl-rewrite --dag-thresh=0 | tail -n +2 > $cvc5pfname
  #timeout 60 veriT --proof-prune --proof-merge --proof-with-sharing --cnf-definitional --disable-ackermann --input=smtlib2 --proof=$veritpfname $relpathsmt
  #To qfuf.v, add
  echo "Section test$ctr." >> $qfuf
  echo "  Goal True. idtac \"\". idtac \"$abspathcoq\". Abort." >> $qfuf
  echo "  Verit_Checker \"$abspathsmt\" \"$abspathveritpf\"." >> $qfuf
  echo "End test$ctr." >> $qfuf
  echo "" >> $qfuf
  
  echo "Add Rec LoadPath \"/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src\" as SMTCoq." > $abspathcoq
  echo "Require Import SMTCoq.SMTCoq." >> $abspathcoq
  echo "Require Import Bool." >> $abspathcoq
  echo "" >> $abspathcoq
  echo "" >> $abspathcoq
  echo "Section test$ctr." >> $abspathcoq
  echo "  Goal True. idtac \"\". idtac \"$abspathsmt\". Abort." >> $abspathcoq
  echo "  Verit_Checker \"$abspathsmt\" \"$abspathveritpf\"." >> $abspathcoq
  echo "End test$ctr." >> $abspathcoq
  echo "" >> $qfuf
  
  echo "coqc $abspathcoq" >> $coqclist
  
  ctr=$((ctr+1))
  echo ""
done;
