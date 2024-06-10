#!/usr/bin/python3
import os
import shutil
path = input('Enter directory path: ')
name = input('Enter file name without extension: ')

pathsmt = path + name + ".smt2"
pathpf = path + name + ".pf"
pathcoq = path + name + ".v"

f = open(pathcoq, "w")
f.write("Add Rec LoadPath \"/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src\" as SMTCoq.\n")
f.write("Require Import SMTCoq.SMTCoq.\n")
f.write("Require Import Bool.\n")
f.write("Section Benchmark.\n")
f.write("  Verit_Checker \"" + pathsmt + "\" \"" + pathpf + "\".\n")
f.write("End Benchmark.\n")
f.close()

n = input('Enter a number for the variables: ')
fname = path + name + "debug.v"
f = open(fname, "w")
f.write("Add Rec LoadPath \"/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src\" as SMTCoq.\n")
f.write("Require Import SMTCoq.SMTCoq.\n")
f.write("Require Import Bool.\n")
f.write("Require Import Int31.\n")
f.write("Local Open Scope int31_scope.\n\n")
f.write("Section Test" + name + "Debug.\n")
f.write("  Parse_certif_verit t_i" + n + " t_func" + n + " t_atom" + n + " t_form" + n + " root" + n + " used_roots" + n + " trace" + n + "\n")
f.write("  \"" + pathsmt + "\"\n")
f.write("  \"" + pathpf + "\".\n")
f.write("  Definition nclauses" + n + " := Eval vm_compute in (match trace" + n + " with Certif a _ _ => a end). (* Size of the state *)\n")
f.write("  Print nclauses" + n + ".\n")
f.write("  Definition c" + n + " := Eval vm_compute in (match trace" + n + " with Certif _ a _ => a end). (* Certificate *)\n")
f.write("  Print c" + n + ".\n")
f.write("  Definition conf" + n + " := Eval vm_compute in (match trace" + n + " with Certif _ _ a => a end). (* Look here in the state for the empty clause*)\n")
f.write("  Print conf" + n + ".\n")
f.write("  Eval vm_compute in List.length (fst c" + n + "). (* No. of steps in certificate *)\n")
f.write("  (* Sanity check that atoms and formulas are well-typed. Must return true *)\n")
f.write("  Eval vm_compute in (Form.check_form t_form" + n + " && Atom.check_atom t_atom" + n + " && Atom.wt t_i" + n + " t_func" + n + " t_atom" + n + ").\n\n\n")

f.write("  (* States from c" + n + " *)\n\n")

f.write("  (* Start state *)\n")
f.write("  Definition s0_" + n + " := Eval vm_compute in (add_roots (S.make nclauses" + n + ") root" + n + " used_roots" + n + ").\n")
f.write("  Print s0_" + n + ".\n")
f.write("  (* s0_" + n + " = ({|  |} *)\n")
f.close()
print("Now open file " + fname + " in Coqide, check the number of steps in the certificate.\n")
f = open(fname, "a")
sn = input('Enter number of steps in certificate: ')
for i in range(int(sn)):
  si = str(int(i) + 1)
  i_str = str(i)
  f.write("  Eval vm_compute in List.nth " + i_str + " (fst c" + n + ") _.\n")
  f.write("  (* " + si + ". *)\n")
  f.write("  Definition s" + si + "_" + n + " := Eval vm_compute in (step_checker s" + i_str + "_" + n + " (List.nth " + i_str + " (fst c" + n + ") (CTrue t_func" + n + " t_atom" + n + " t_form" + n + " 0))).\n")
  f.write("  Print s" + si + "_" + n + ".\n")
  f.write("  (* s" + si + "_" + n + " = ({|  |} *)\n\n")
f.write("End Test" + n + "Debug.\n")
f.close()
