#!/bin/bash
cd test1
echo "Test 1 VeriT"
coqc test1verit.v
echo "Test 1 cvc5"
coqc test1cvc5.v
cd ..

cd test2
echo "Test 2 VeriT"
coqc test2verit.v
echo "Test 2 cvc5"
coqc test2cvc5.v
cd ..

cd test3
echo "Test 3 VeriT"
coqc test3verit.v
echo "Test 3 cvc5"
coqc test3cvc5.v
cd ..

cd test4
echo "Test 4 VeriT"
coqc test4verit.v
echo "Test 4 cvc5"
coqc test4cvc5.v
cd ..

cd test5
echo "Test 5 VeriT"
coqc test5verit.v
echo "Test 5 cvc5"
coqc test5cvc5.v
cd ..

cd test6
echo "Test 6 VeriT"
coqc test6verit.v
echo "Test 6 cvc5"
coqc test6cvc5.v
cd ..

cd test7
echo "Test 7 VeriT"
coqc test7verit.v
echo "Test 7 cvc5"
coqc test7cvc5.v
cd ..

cd test8
echo "Test 8 VeriT"
coqc test8verit.v
echo "Test 8 cvc5"
coqc test8cvc5.v
cd ..
