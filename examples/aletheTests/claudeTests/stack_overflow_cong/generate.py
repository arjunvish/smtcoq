#!/usr/bin/env python3
"""Generates a .cvc5pf with a long, genuinely-needed refutation (a0/r0/tFinal) followed by
N independent, otherwise-unused genuine `cong` derivations (each: refl x=x, then cong deriving
not(x)=not(x) from it). Demonstrates the process_cong stack-overflow fix: the pre-fix
process_cong_aux recursed non-tail-recursively once per *any* certificate step (cong or not),
building one native stack frame per step before returning, so a long enough certificate
overflows the stack regardless of what the filler steps actually do - genuine `cong` steps are
used here just to keep the file on-topic for process_cong specifically.

Usage: python3 generate.py N > stack_overflow_cong.cvc5pf
"""
import sys

n = int(sys.argv[1]) if len(sys.argv) > 1 else 4000

print("(assume a0 (not (= x x)))")
print("(step r0 (cl (= x x)) :rule refl)")
for i in range(1, n + 1):
    print(f"(step a{i} (cl (= x x)) :rule refl)")
    print(f"(step c{i} (cl (= (not x) (not x))) :rule cong :premises (a{i}))")
print("(step tFinal (cl) :rule resolution :premises (a0 r0))")
