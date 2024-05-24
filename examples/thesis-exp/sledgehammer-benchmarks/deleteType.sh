#!/bin/bash
#Search all *.smt_in files for "exists". For every match x, remove the smt_in file and the corresponding smt_inproofnew file
for f in `find . -name "*.smt_in"`;
do
  #Look for rulename
  if grep -q "$1" $f
  then
  	prooffile="${f}proofnew"
  	rm "$prooffile"
  	rm "$f"
  fi
done
