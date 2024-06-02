#!/bin/bash
# For each .smt_in files in the directory, 
#   Run cvc5 on it, get the proof in a .cvc5pf file
#   Add a statement to check the file with its corresponding .cvc5pf file to sledgehammercvc5.v and also create a *.v file that independently checks this file
#   Add a call to coqc on the independent files to script cvccoqc.sh so that they can be called independently

#Headers of scripts to call coqc
cvccoqc="cvc5oldcoqc.sh"
echo "#!/bin/bash" > $cvccoqc
echo "" >> $cvccoqc
#veritcoqc="veritcoqc.sh"
#echo "#!/bin/bash" > $veritcoqc
#echo "" >> $veritcoqc

#Headers of coq files that call all tests
shcvc="sledgehammercvc5.v"
#shverit="sledgehammerverit.v"

#To sledgehammer.v, add the following lines
echo "Add Rec LoadPath \"/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src\" as SMTCoq." > $shcvc
echo "Require Import SMTCoq.SMTCoq." >> $shcvc
echo "Require Import Bool." >> $shcvc
echo "" >> $shcvc
echo "" >> $shcvc
#echo "Add Rec LoadPath \"/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src\" as SMTCoq." > $shverit
#echo "Require Import SMTCoq.SMTCoq." >> $shverit
#echo "Require Import Bool." >> $shverit
#echo "" >> $shverit
#echo "" >> $shverit

ctr=1
for relpathsmt in $(find ./ -name '*.smt_in'); do
  #Create relative and absolute paths for each file
  echo "Relative Path: $relpathsmt"
  abspathsmt=$(realpath $relpathsmt)
  echo "Absolute Path: $abspathsmt"
  abspathcvcpf=${abspathsmt/\.smt_in/\.cvc5oldpf}
  echo "Absolute Path of cvc Proof File: $abspathcvcpf"
  abspathcvccoq=${abspathsmt%.smt_in}cvc5.v
  echo "Absolute Path of cvc Coq File: $abspathcvccoq"
  #abspathveritpf=${abspathsmt/\.smt_in/\.smt_inproofnew}
  #echo "Absolute Path of verit Proof File: $abspathveritpf"
  #abspathveritcoq=${abspathsmt%.smt_in}verit.v
  #echo "Absolute Path of verit Coq File: $abspathveritcoq"
  
  #Call solver to create proof
  timeout 30 cvc5-pn-old $relpathsmt --dump-proof --proof-format=alethe --proof-granularity=dsl-rewrite --dag-thresh=0 --lang=smtlib2 | tail -n +2 | sed ':a; /^\n*$/{$d; N;}; /\n$/ba' > $abspathcvcpf #first line of output has `unsat` and there are trailing empty lines in the end which need to be removed for the Coq checker

  #Add a section and call to the checker to the sh files
  echo "Section test$ctr." >> $shcvc
  echo "  Goal True. idtac \"\". idtac \"$abspathcvccoq\". Abort." >> $shcvc
  echo "  Lfsc_Checker \"$abspathsmt\" \"$abspathcvcpf\"." >> $shcvc
  echo "End test$ctr." >> $shcvc
  echo "" >> $shcvc
  #echo "Section test$ctr." >> $shverit
  #echo "  Goal True. idtac \"\". idtac \"$abspathveritcoq\". Abort." >> $shverit
  #echo "  Lfsc_Checker \"$abspathsmt\" \"$abspathveritpf\"." >> $shverit
  #echo "End test$ctr." >> $shverit
  #echo "" >> $shverit
  
  #Create the indpendent .v file for each call
  echo "Add Rec LoadPath \"/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src\" as SMTCoq." > $abspathcvccoq
  echo "Require Import SMTCoq.SMTCoq." >> $abspathcvccoq
  echo "Require Import Bool." >> $abspathcvccoq
  echo "" >> $abspathcvccoq
  echo "" >> $abspathcvccoq
  echo "Section test$ctr." >> $abspathcvccoq
  echo "  Goal True. idtac \"\". idtac \"$abspathcvccoq\". Abort." >> $abspathcvccoq
  echo "  Verit_Checker \"$abspathsmt\" \"$abspathcvcpf\"." >> $abspathcvccoq
  echo "End test$ctr." >> $abspathcvccoq
  echo "" >> $abspathcvccoq
  #echo "Add Rec LoadPath \"/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src\" as SMTCoq." > $abspathveritcoq
  #echo "Require Import SMTCoq.SMTCoq." >> $abspathveritcoq
  #echo "Require Import Bool." >> $abspathveritcoq
  #echo "" >> $abspathveritcoq
  #echo "" >> $abspathveritcoq
  #echo "Section test$ctr." >> $abspathveritcoq
  #echo "  Goal True. idtac \"\". idtac \"$abspathveritcoq\". Abort." >> $abspathveritcoq
  #echo "  Verit_Checker \"$abspathsmt\" \"$abspathveritpf\"." >> $abspathveritcoq
  #echo "End test$ctr." >> $abspathveritcoq
  #echo "" >> $abspathveritcoq
  #Add a call to the sh files using coqc to the scripts
  echo "coqc $abspathcvccoq" >> $cvccoqc
  #echo "coqc $abspathveritcoq" >> $veritcoqc
  
  ctr=$((ctr+1))
  echo ""
done;
