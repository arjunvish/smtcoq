#!/bin/bash
# For each .smt_in files in the directory, 
#   Run cvc4 on it, get the proof in a .cvc4pf file
#   Run veriT2016 on it, get the proof in a .verit2016pf file
#   Add a statement to check the file with its corresponding .cvc4pf file to sledgehammercvc4.v and also create a *.v file that independently checks this file
#   Add a call to coqc on the independent files to script cvccoqc.sh so that they can be called independently
#   Add a statement to the check the file with its corresponding .verit2016pf file to sledgehammerverit2016.v and also create a *.v file that independently checks this file
#   Add a call to coqc on the independent files to script veritcoqc.sh so that they can be called independently

#Headers of scripts to call coqc
cvccoqc="cvc4coqc.sh"
veritcoqc="verit2016coqc.sh"
echo "#!/bin/bash" > $cvccoqc
echo "" >> $cvccoqc
echo "#!/bin/bash" > $veritcoqc
echo "" >> $veritcoqc

#Headers of coq files that call all tests
shcvc="sledgehammercvc4.v"
shverit="sledgehammerverit2016.v"
#To sledgehammer.v, add the following lines
echo "Add Rec LoadPath \"/home/arjun/Desktop/smtcoq/smtcoq/src\" as SMTCoq." > $shcvc
echo "Require Import SMTCoq.SMTCoq." >> $shcvc
echo "Require Import Bool." >> $shcvc
echo "" >> $shcvc
echo "" >> $shcvc
echo "Add Rec LoadPath \"/home/arjun/Desktop/smtcoq/smtcoq/src\" as SMTCoq." > $shverit
echo "Require Import SMTCoq.SMTCoq." >> $shverit
echo "Require Import Bool." >> $shverit
echo "" >> $shverit
echo "" >> $shverit

ctr=1
for relpathsmt in $(find ./ -name '*.smt_in'); do
  #Create relative and absolute paths for each file
  echo "Relative Path: $relpathsmt"
  abspathsmt=$(realpath $relpathsmt)
  echo "Absolute Path: $abspathsmt"
  abspathcvcpf=${abspathsmt/\.smt_in/\.cvc4pf}
  echo "Absolute Path of cvc Proof File: $abspathcvcpf"
  abspathveritpf=${abspathsmt/\.smt_in/\.verit2016pf}
  echo "Absolute Path of verit Proof File: $abspathveritpf"
  abspathcvccoq=${abspathsmt%.smt_in}cvc4.v
  echo "Absolute Path of cvc Coq File: $abspathcvccoq"
  abspathveritcoq=${abspathsmt%.smt_in}verit2016.v
  echo "Absolute Path of verit Coq File: $abspathveritcoq"

  #Call both solvers to create proofs
  timeout 30 cvc4 $relpathsmt --lang smt2 --proof --dump-proof --simplification=none --fewer-preprocessing-holes --dag-thresh=0 | tail -n +2 > $abspathcvcpf
  timeout 30 veriT --proof-prune --proof-merge --proof-with-sharing --cnf-definitional --disable-ackermann --input=smtlib2 --proof=$abspathveritpf $relpathsmt

  #Add a section and call to the checker to the sh files
  echo "Section test$ctr." >> $shcvc
  echo "  Goal True. idtac \"\". idtac \"$abspathcvccoq\". Abort." >> $shcvc
  echo "  Lfsc_Checker \"$abspathsmt\" \"$abspathcvcpf\"." >> $shcvc
  echo "End test$ctr." >> $shcvc
  echo "" >> $shcvc
  echo "Section test$ctr." >> $shverit
  echo "  Goal True. idtac \"\". idtac \"$abspathveritcoq\". Abort." >> $shverit
  echo "  Verit_Checker \"$abspathsmt\" \"$abspathveritpf\"." >> $shverit
  echo "End test$ctr." >> $shverit
  echo "" >> $shverit

  #Create the indpendent .v file for each call
  echo "Add Rec LoadPath \"/home/arjun/Desktop/smtcoq/smtcoq/src\" as SMTCoq." > $abspathcvccoq
  echo "Require Import SMTCoq.SMTCoq." >> $abspathcvccoq
  echo "Require Import Bool." >> $abspathcvccoq
  echo "" >> $abspathcvccoq
  echo "" >> $abspathcvccoq
  echo "Section test$ctr." >> $abspathcvccoq
  echo "  Goal True. idtac \"\". idtac \"$abspathcvccoq\". Abort." >> $abspathcvccoq
  echo "  Lfsc_Checker \"$abspathsmt\" \"$abspathcvcpf\"." >> $abspathcvccoq
  echo "End test$ctr." >> $abspathcvccoq
  echo "" >> $abspathcvccoq
  echo "Add Rec LoadPath \"/home/arjun/Desktop/smtcoq/smtcoq/src\" as SMTCoq." > $abspathveritcoq
  echo "Require Import SMTCoq.SMTCoq." >> $abspathveritcoq
  echo "Require Import Bool." >> $abspathveritcoq
  echo "" >> $abspathveritcoq
  echo "" >> $abspathveritcoq
  echo "Section test$ctr." >> $abspathveritcoq
  echo "  Goal True. idtac \"\". idtac \"$abspathveritcoq\". Abort." >> $abspathveritcoq
  echo "  Verit_Checker \"$abspathsmt\" \"$abspathveritpf\"." >> $abspathveritcoq
  echo "End test$ctr." >> $abspathveritcoq
  echo "" >> $abspathveritcoq
  
  #Add a call to the sh files using coqc to the scripts
  echo "coqc $abspathcvccoq" >> $cvccoqc
  echo "coqc $abspathveritcoq" >> $veritcoqc
  
  ctr=$((ctr+1))
  echo ""
done;
