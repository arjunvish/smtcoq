#!/bin/bash
# For each .smt_in files in the directory, 
#   Run cvc5 on it, get the proof in a .cvc5pf file
#   Add a statement to check the file with its corresponding .cvc5pf file to sledgehammercvc5.v and also create a *.v file that independently checks this file
#   Add a call to coqc on the independent files to script cvccoqc.sh so that they can be called independently

#Headers of scripts to call coqc
cvccoqc="cvc5coqc.sh"
echo "#!/bin/bash" > $cvccoqc
echo "" >> $cvccoqc

#Headers of coq files that call all tests
shcvc="sledgehammercvc5.v"

#To sledgehammer.v, add the following lines
echo "Add Rec LoadPath \"/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src\" as SMTCoq." > $shcvc
echo "Require Import SMTCoq.SMTCoq." >> $shcvc
echo "Require Import Bool." >> $shcvc
echo "" >> $shcvc
echo "" >> $shcvc

ctr=1
for relpathsmt in $(find ./ -name '*.smt_in'); do
  #Create relative and absolute paths for each file
  echo "Relative Path: $relpathsmt"
  abspathsmt=$(realpath $relpathsmt)
  echo "Absolute Path: $abspathsmt"
  abspathcvcpf=${abspathsmt/\.smt_in/\.cvc5pf}
  echo "Absolute Path of cvc Proof File: $abspathcvcpf"
  abspathcvccoq=${abspathsmt%.smt_in}cvc5.v
  echo "Absolute Path of cvc Coq File: $abspathcvccoq"
  
  #Call solver to create proof
  timeout 30 cvc5-pn $relpathsmt --dump-proof --proof-format=alethe --dag-thresh=0 | tail -n +2 > $abspathcvcpf

  #Add a section and call to the checker to the sh files
  echo "Section test$ctr." >> $shcvc
  echo "  Goal True. idtac \"\". idtac \"$abspathcvccoq\". Abort." >> $shcvc
  echo "  Lfsc_Checker \"$abspathsmt\" \"$abspathcvcpf\"." >> $shcvc
  echo "End test$ctr." >> $shcvc
  echo "" >> $shcvc
  
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
  
  #Add a call to the sh files using coqc to the scripts
  echo "coqc $abspathcvccoq" >> $cvccoqc
  
  ctr=$((ctr+1))
  echo ""
done;
