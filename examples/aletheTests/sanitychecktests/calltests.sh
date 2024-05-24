#!/bin/bash
echo "Test 1 VeriT"
coqc ./test1/test1verit.v
echo "Test 1 cvc5"
coqc ./test1/test1cvc5.v

echo "Test 2 VeriT"
coqc ./test2/test2verit.v
echo "Test 2 cvc5"
coqc ./test2/test2cvc5.v

echo "Test 3 VeriT"
coqc ./test3/test3verit.v
echo "Test 3 cvc5"
coqc ./test3/test3cvc5.v

echo "Test 4 VeriT"
coqc ./test4/test4verit.v
echo "Test 4 cvc5"
coqc ./test4/test4cvc5.v

echo "Test 5 VeriT"
coqc ./test5/test5verit.v
echo "Test 5 cvc5"
coqc ./test5/test5cvc5.v

echo "Test 6 VeriT"
coqc ./test6/test6verit.v
echo "Test 6 cvc5"
coqc ./test6/test6cvc5.v

echo "Test 7 VeriT"
coqc ./test7/test7verit.v
echo "Test 7 cvc5"
coqc ./test7/test7cvc5.v

echo "Test 8 VeriT"
coqc ./test8/test8verit.v
echo "Test 8 cvc5"
coqc ./test8/test8cvc5.v
