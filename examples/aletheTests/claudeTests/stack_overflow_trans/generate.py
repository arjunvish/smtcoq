#!/usr/bin/env python3
"""Generates a .cvc5pf with a long, genuinely-needed refutation (a0/r0/tFinal) followed by
N independent, otherwise-unused genuine `trans` derivations (each: two refl facts x=x, then
trans deriving x=x from them again - a genuine, if repetitive, use of the TransAST rule).
Demonstrates the process_trans stack-overflow fix, the same way stack_overflow_cong.cvc5pf
demonstrates it for process_cong - see the comment there and in CLAUDE.md for the general
mechanism.

Usage: python3 generate.py N > stack_overflow_trans.cvc5pf
"""
import sys

n = int(sys.argv[1]) if len(sys.argv) > 1 else 4000

print("(assume a0 (not (= x x)))")
print("(step r0 (cl (= x x)) :rule refl)")
for i in range(1, n + 1):
    print(f"(step a{i} (cl (= x x)) :rule refl)")
    print(f"(step b{i} (cl (= x x)) :rule refl)")
    print(f"(step t{i} (cl (= x x)) :rule trans :premises (a{i} b{i}))")
print("(step tFinal (cl) :rule resolution :premises (a0 r0))")
