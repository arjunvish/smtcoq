'''
This script is for generating the run.v file
'''

#Import parse functions
from parse_functions import *

#Get first command line argument into a string variable
import sys 
import os
import subprocess
from enum import Enum
import re

#Defining files 
i = sys.argv[1]
base_name = os.path.basename(i)
full_name = base_name + "/" + i + "run.v"
smt_name = base_name + "/" +i + ".smt2"
parse_name = base_name + "/" +i + ".txt"
pf_name = base_name + "/" +i + ".pf"

'''
try:
    solver = sys.argv[2]
except IndexError:
    # no second arg, no problem
    pf_name = base_name + "/" +i + ".pf"
else:
    if(sys.argv[2]):
        solver = sys.argv[2]
        if(solver == "cvc5" or solver == "cvc4" or solver == "veriT" or solver == "veriT-old"):
            pf_name = base_name + "/" +i + solver + ".pf"
        else:
            raise ValueError:
                print("Second argument is an invalid solver. Must be 'cvc5', 'cvc4', 'veriT', or 'veriT-old'.\nGiven: " + solver)

'''

'''
Takes 1. a string - the Coq debug file name
      Runs coqc on the debug file, returns output as a string
'''
def run_coqc(fname):
    coqc = subprocess.run(['coqc', fname], text=True, capture_output=True)
    coqcop = coqc.stdout #output to be parsed
    return coqcop

'''
Takes 1. an file - the coq debug file
    Writes the inital lines for a debug file
'''
def initialWrite(f):
    f.write(
        "Add Rec LoadPath \"../../src\" as SMTCoq.\n"
        "Require Import SMTCoq.SMTCoq.\n"
        "Require Import Bool. \n" 
        "Require Import Int31. \n"  
        "Local Open Scope int31_scope.\n"
        "\n"
        "Section " + base_name + "debug. \n" 
            "\n"
            " " + "Parse_certif_verit t_i t_func t_atom t_form root used_roots trace \n"
            " \"" + smt_name + "\" \n"
            " \"" + pf_name + "\". \n"
            "\n"
            " " + "Definition nclauses := Eval vm_compute in (match trace with Certif a _ _ => a end). (* Size of the state *)\n"
            " " + "Print nclauses.\n"
        )
        
    f.write("\n " + " " + "Definition c := Eval vm_compute in (match trace with Certif _ a _ => a end). (* Certificate *)\n" + " " + "Definition conf := Eval vm_compute in (match trace with Certif _ _ a => a end). (* Look here in the state for the empty clause*)\n" + " " + "Print conf.\n")   
    f.write("\n" + " " + "Eval vm_compute in List.length (fst c). (* No. of steps in certificate *) \n" )



'''
Code to:
1. Create debug file, 'full_name'
2. Open and write initial debug code
3. Write initial debug code
4. Close file and run coq, extract number of steps in certificate
5. Write remaining debug code using the steps in certificate
6. Close file and run coq
'''
def main():
    #empty file
    with open(full_name, "w") as f:
        f.close()

    with open(full_name, "r+") as f:      
        #inital debug code
        initialWrite(f)
        f.write("End " + base_name + "debug.")

    ## Run coqc and extract num steps    
    coq_op = run_coqc(full_name)
    certnum = parse_coq_certnum(coq_op) # number of steps in certificate



    ## Write remaining debug code
    #empty file
    with open(full_name, "w") as f:
        f.close
    
    with open(full_name, "r+") as f:
        initialWrite(f)

        #up to s0
        f.write("\n Eval vm_compute in (Form.check_form t_form && Atom.check_atom t_atom && Atom.wt t_i t_func t_atom).\n")
        f.write("\n Definition s0 := Eval vm_compute in (add_roots (S.make nclauses) root used_roots).\n")
        f.write(" Print s0.\n")
        
        #states up to certnum
        for i in range(certnum):
            f.write("\n" + " " +  "Eval vm_compute in List.nth " + str(i) + " (fst c) _.\n")
            f.write("\n" + " " + "Definition s" + str(i + 1) + " := Eval vm_compute in (step_checker s" + str(i) + " (List.nth " + str(i) + " (fst c) (CTrue t_func t_atom t_form 0))). \n" + " " + "Print s" + str(i + 1) + ". \n")
            f.write("\n")
        f.write("End " + base_name + "debug.")


if __name__ == "__main__":
    main()