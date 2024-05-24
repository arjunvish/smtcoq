(set-info :smt-lib-version 2.6)
(set-logic QF_UF)
(set-info :source |
Generated by: Aman Goel (amangoel@umich.edu), Karem A. Sakallah (karem@umich.edu)
Generated on: 2018-04-06

Generated by the tool Averroes 2 (successor of [1]) which implements safety property
verification on hardware systems.

This SMT problem belongs to a set of SMT problems generated by applying Averroes 2
to benchmarks derived from [2-5].

A total of 412 systems (345 from [2], 19 from [3], 26 from [4], 22 from [5]) were
syntactically converted from their original formats (using [6, 7]), and given to 
Averroes 2 to perform property checking with abstraction (wide bit-vectors -> terms, 
wide operators -> UF) using SMT solvers [8, 9].

[1] Lee S., Sakallah K.A. (2014) Unbounded Scalable Verification Based on Approximate
Property-Directed Reachability and Datapath Abstraction. In: Biere A., Bloem R. (eds)
Computer Aided Verification. CAV 2014. Lecture Notes in Computer Science, vol 8559.
Springer, Cham
[2] http://fmv.jku.at/aiger/index.html#beem
[3] http://www.cs.cmu.edu/~modelcheck/vcegar
[4] http://www.cprover.org/hardware/v2c
[5] http://github.com/aman-goel/verilogbench
[6] http://www.clifford.at/yosys
[7] http://github.com/chengyinwu/V3
[8] http://github.com/Z3Prover/z3
[9] http://github.com/SRI-CSL/yices2

id: counter_v
query-maker: "Yices 2"
query-time: 0.002000 ms
query-class: abstract
query-category: oneshot
query-type: regular
status: unsat
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")

;
(set-info :status unsat)
(declare-sort uttDOLLAR4 0)
(declare-fun Add_4_4_4 (uttDOLLAR4 uttDOLLAR4 ) uttDOLLAR4)
(declare-fun yDOLLAR13 () Bool)
(declare-fun yDOLLAR16 () Bool)
(declare-fun yDOLLAR17 () Bool)
(declare-fun yDOLLAR2 () Bool)
(declare-fun yDOLLAR25 () Bool)
(declare-fun yDOLLAR26 () Bool)
(declare-fun yDOLLAR27 () Bool)
(declare-fun yDOLLAR28 () Bool)
(declare-fun yDOLLAR29 () Bool)
(declare-fun yDOLLAR30 () Bool)
(declare-fun yDOLLAR33 () Bool)
(declare-fun yDOLLAR34 () Bool)
(declare-fun yDOLLAR37 () Bool)
(declare-fun yDOLLAR42 () Bool)
(declare-fun yDOLLAR43 () Bool)
(declare-fun yDOLLAR44 () Bool)
(declare-fun yDOLLAR45 () Bool)
(declare-fun yDOLLAR58 () Bool)
(declare-fun yDOLLAR6 () Bool)
(declare-fun yDOLLARX () uttDOLLAR4)
(declare-fun yDOLLARXDOLLARnext () uttDOLLAR4)
(declare-fun yDOLLARXDOLLARnext_rhs () uttDOLLAR4)
(declare-fun yDOLLARXDOLLARnext_rhs_op () uttDOLLAR4)
(declare-fun yDOLLARen () Bool)
(declare-fun yDOLLARn15s4 () uttDOLLAR4)
(declare-fun yDOLLARn1s4 () uttDOLLAR4)
(declare-fun yDOLLARprop () Bool)
(declare-fun yDOLLARpropDOLLARnext () Bool)
(declare-fun yDOLLARsDOLLAR1 () uttDOLLAR4)
(declare-fun yDOLLARsDOLLAR1DOLLARnext () uttDOLLAR4)
(declare-fun yDOLLARsDOLLAR1DOLLARnext_op () uttDOLLAR4)
(declare-fun yDOLLARsDOLLAR1_op () uttDOLLAR4)
(declare-fun yDOLLARsDOLLAR4 () uttDOLLAR4)
(declare-fun yDOLLARsDOLLAR4_op () uttDOLLAR4)
(assert (not (= yDOLLARn1s4 yDOLLARn15s4)))
(assert (= yDOLLAR2 (= yDOLLARn1s4 yDOLLARX)))
(assert (= (= yDOLLARn15s4 yDOLLARX) yDOLLAR6))
(assert (= yDOLLARsDOLLAR1_op (Add_4_4_4 yDOLLARX yDOLLARn1s4)))
(assert (= yDOLLARsDOLLAR4_op (ite yDOLLAR6 yDOLLARn1s4 yDOLLARsDOLLAR1_op)))
(assert (= yDOLLARXDOLLARnext_rhs_op (ite yDOLLARen yDOLLARsDOLLAR4_op yDOLLARX)))
(assert (= yDOLLAR13 (= yDOLLARXDOLLARnext yDOLLARXDOLLARnext_rhs_op)))
(assert (= yDOLLAR27 (not (= yDOLLARn15s4 yDOLLARXDOLLARnext))))
(assert (= yDOLLAR28 (= yDOLLARpropDOLLARnext yDOLLAR27)))
(assert (= yDOLLARpropDOLLARnext (not yDOLLAR26)))
(assert (= yDOLLAR34 (= yDOLLARn1s4 yDOLLARXDOLLARnext)))
(assert (= yDOLLARsDOLLAR1DOLLARnext_op (Add_4_4_4 yDOLLARXDOLLARnext yDOLLARn1s4)))
(assert (= yDOLLAR37 (= yDOLLARn15s4 yDOLLARsDOLLAR1DOLLARnext_op)))
(assert (= yDOLLAR43 (and yDOLLAR34 yDOLLAR37)))
(assert (= yDOLLAR43 (not yDOLLAR45)))
(assert (= yDOLLAR33 (= yDOLLARn15s4 yDOLLARsDOLLAR1_op)))
(assert (= yDOLLAR42 (and yDOLLAR2 yDOLLAR33)))
(assert (= yDOLLAR42 (not yDOLLAR44)))
(assert (= yDOLLAR58 (and yDOLLAR2 yDOLLAR13 yDOLLAR28 yDOLLAR26 yDOLLAR45 yDOLLAR44)))
(assert yDOLLAR58)
(check-sat)
(exit)
