#!/bin/bash

echo '' > sledgehammerTests.v
echo 'Add Rec LoadPath "/home/arjun/Desktop/smtcoq-veritAst/smtcoq/src" as SMTCoq.' >> sledgehammerTests.v
echo 'Require Import SMTCoq.SMTCoq.' >> sledgehammerTests.v
echo 'Require Import Bool.' >> sledgehammerTests.v
i=1
#Go through each smt_in file and print the Verit_Checker call for it.
for f in `find ./Benchmarks/ -name "*.smt_in"`;
do
  f1=${f#"./"}
  echo "Section Subproof$i." >> sledgehammerTests.v
  echo "  Verit_Checker \"../examples/${f1}\" \"../examples/${f1}proofnew\"." >> sledgehammerTests.v
  echo "End Subproof$i." >> sledgehammerTests.v
  echo '' >> sledgehammerTests.v
  let i=i+1
done
