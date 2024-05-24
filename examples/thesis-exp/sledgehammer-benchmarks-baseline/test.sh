#!/bin/bash

file=$1
cvc4=$(ulimit -t 12 && ~/Documents/isabelle/prover/CVC4/build/bin/cvc4 --full-saturate-quant --inst-when=full-last-call --inst-no-entail --term-db-mode=relevant --multi-trigger-linear --random-seed=1 --lang=smt2 --tlimit=12000 -L smt2 $file)
echo "$file"

if [[ "$cvc4" == *"unsat"* ]]
then
    echo "CVC4: unsat"
    exit
else
if [[ "$cvc4" == *"sat"* ]]
then
    echo "CVC4: sat"
    rm -f $file
    exit
fi
fi

verit=$(ulimit -t 12 && ~/Documents/repos/verit-rmx/veriT --proof-with-sharing --index-fresh-sorts --proof-define-skolems --proof-prune --proof-merge --disable-print-success --disable-banner --max-time=13  $file)
echo "$file"

if [[ "$verit" == *"unsat"* ]]
then
    echo "VERIT: unsat"
    exit
else
if [[ "$verit" == *"sat"* ]]
then
    echo "VERIT: sat"
    rm -f $file
    exit
fi
fi


z3=$(ulimit -t 12 && ~/.isabelle/contrib/z3-4.4.0pre-3/x86_64-linux/z3 smt.random_seed=1 smt.refine_inj_axioms=false -T:12 $file)
echo "$file"

if [[ "$z3" == *"not unsat"* ]]
then
    echo "Z3: not unsat"
    rm -f $file
    exit
else
if [[ "$z3" == *"unsat"* ]]
then
    echo "Z3: unsat"
    exit
else
    echo "Z3: not unsat"
    rm -f $file
    exit
fi
fi
fi


