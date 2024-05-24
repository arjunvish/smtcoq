#!/bin/bash
#Go through each smt_inproofnew file and print all the rules used.
echo '' > listOfRules
for f in `find . -name "*.smt_inproofnew"`;
do
  grep -o "rule [a-z_]*" $f >> listOfRules
done
