(* Demonstrates the process_cong stack-overflow fix. stack_overflow_cong.cvc5pf is generated
   by generate.py: a small, genuinely-needed refutation (a0/r0/tFinal) followed by N independent
   `refl` + `cong` pairs (each deriving "not(x)=not(x)" from "x=x" - a genuine, if repetitive,
   use of the CongAST "not"-congruence rule), none of which the refutation actually needs. The
   old process_cong_aux recursed as `step :: process_cong_aux tl cog` for *every* certificate
   step (not just cong ones), which is not a tail call in OCaml - each step adds a native stack
   frame that can't be reclaimed until the whole rest of the certificate has been processed and
   returned. On a long enough certificate this overflows the stack outright, well before the
   checker gets anywhere near evaluating soundness.
   While calibrating N for this file, the same "instant Stack_overflow, well under a second"
   symptom kept reappearing even after process_cong (and everything else already listed as
   fixed elsewhere in this file/CLAUDE.md) was confirmed fixed - it turned out store_shared_terms,
   process_fins, process_hole, process_proj, and process_notnot (all *earlier* passes in
   preprocess_certif's pipeline, run before process_cong ever sees the certificate) had the
   exact same non-tail-recursive shape and had never been touched by the original fix. They're
   now fixed the same way. N=4000 here is picked to run in a few seconds on the fixed code
   while still being far beyond any of these functions' pre-fix stack limits; scale N up if it
   doesn't overflow the stack on your system, but note checking time scales worse than linearly
   with N even on the fixed code (this file's proof structure is a worst case: many small,
   entirely independent steps, none of which get pruned by process_unused), so very large N may
   just time out instead of demonstrating anything new. *)

Add Rec LoadPath "../../../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.

Section StackOverflowCong.
  Verit_Checker "stack_overflow_cong.smt2" "stack_overflow_cong.cvc5pf".
End StackOverflowCong.
