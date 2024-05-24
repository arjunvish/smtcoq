Add Rec LoadPath "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool.
Require Import Int31.
Local Open Scope int31_scope.

Section Testtest7cvc5Debug.
  Parse_certif_verit t_i1 t_func1 t_atom1 t_form1 root1 used_roots1 trace1
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test7/test7cvc5.smt2"
  "/home/arjun/Desktop/smtcoq/arjunvish-smtcoq-veritAst/smtcoq/examples/aletheTests/sanitychecktests/test7/test7cvc5.pf".
  Definition nclauses1 := Eval vm_compute in (match trace1 with Certif a _ _ => a end). (* Size of the state *)
  Print nclauses1.
  Definition c1 := Eval vm_compute in (match trace1 with Certif _ a _ => a end). (* Certificate *)
  Print c1.
  Definition conf1 := Eval vm_compute in (match trace1 with Certif _ _ a => a end). (* Look here in the state for the empty clause*)
  Print conf1.
  Eval vm_compute in List.length (fst c1). (* No. of steps in certificate *)
  (* Sanity check that atoms and formulas are well-typed. Must return true *)
  Eval vm_compute in (Form.check_form t_form1 && Atom.check_atom t_atom1 && Atom.wt t_i1 t_func1 t_atom1).


  (* States from c1 *)

  (* Start state *)
  Definition s0_1 := Eval vm_compute in (add_roots (S.make nclauses1) root1 used_roots1).
  Print s0_1.
  (* s0_1 = ({| 0 <- [31] |} *)
  Eval vm_compute in List.nth 0 (fst c1) _.
  (* 1. BuildDef2 1 41 *)
  Definition s1_1 := Eval vm_compute in (step_checker s0_1 (List.nth 0 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s1_1.
  (* s1_1 = ({| 0 <- [31], 1 <- [30; 39; 41]  |} *)

  Eval vm_compute in List.nth 1 (fst c1) _.
  (* 2. LiaMicromega 2 [46] *)
  Definition s2_1 := Eval vm_compute in (step_checker s1_1 (List.nth 1 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s2_1.
  (* s2_1 = ({|  |} *)

  Eval vm_compute in List.nth 2 (fst c1) _.
  (* 3. *)
  Definition s3_1 := Eval vm_compute in (step_checker s2_1 (List.nth 2 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s3_1.
  (* s3_1 = ({|  |} *)

  Eval vm_compute in List.nth 3 (fst c1) _.
  (* 4. *)
  Definition s4_1 := Eval vm_compute in (step_checker s3_1 (List.nth 3 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s4_1.
  (* s4_1 = ({|  |} *)

  Eval vm_compute in List.nth 4 (fst c1) _.
  (* 5. *)
  Definition s5_1 := Eval vm_compute in (step_checker s4_1 (List.nth 4 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s5_1.
  (* s5_1 = ({|  |} *)

  Eval vm_compute in List.nth 5 (fst c1) _.
  (* 6. *)
  Definition s6_1 := Eval vm_compute in (step_checker s5_1 (List.nth 5 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s6_1.
  (* s6_1 = ({|  |} *)

  Eval vm_compute in List.nth 6 (fst c1) _.
  (* 7. *)
  Definition s7_1 := Eval vm_compute in (step_checker s6_1 (List.nth 6 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s7_1.
  (* s7_1 = ({|  |} *)

  Eval vm_compute in List.nth 7 (fst c1) _.
  (* 8. *)
  Definition s8_1 := Eval vm_compute in (step_checker s7_1 (List.nth 7 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s8_1.
  (* s8_1 = ({|  |} *)

  Eval vm_compute in List.nth 8 (fst c1) _.
  (* 9. *)
  Definition s9_1 := Eval vm_compute in (step_checker s8_1 (List.nth 8 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s9_1.
  (* s9_1 = ({|  |} *)

  Eval vm_compute in List.nth 9 (fst c1) _.
  (* 10. *)
  Definition s10_1 := Eval vm_compute in (step_checker s9_1 (List.nth 9 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s10_1.
  (* s10_1 = ({|  |} *)

  Eval vm_compute in List.nth 10 (fst c1) _.
  (* 11. *)
  Definition s11_1 := Eval vm_compute in (step_checker s10_1 (List.nth 10 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s11_1.
  (* s11_1 = ({|  |} *)

  Eval vm_compute in List.nth 11 (fst c1) _.
  (* 12. *)
  Definition s12_1 := Eval vm_compute in (step_checker s11_1 (List.nth 11 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s12_1.
  (* s12_1 = ({|  |} *)

  Eval vm_compute in List.nth 12 (fst c1) _.
  (* 13. *)
  Definition s13_1 := Eval vm_compute in (step_checker s12_1 (List.nth 12 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s13_1.
  (* s13_1 = ({|  |} *)

  Eval vm_compute in List.nth 13 (fst c1) _.
  (* 14. *)
  Definition s14_1 := Eval vm_compute in (step_checker s13_1 (List.nth 13 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s14_1.
  (* s14_1 = ({|  |} *)

  Eval vm_compute in List.nth 14 (fst c1) _.
  (* 15. Res 7 {| 0 <- 7, 1 <- 5 |} *)
  Definition s15_1 := Eval vm_compute in (step_checker s14_1 (List.nth 14 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s15_1.
  (* s15_1 = ({| 0 <- [31], 1 <- [30; 39; 41], 2 <- [46], 3 <- [48], 4 <- [8; 51], 5 <- [0], 6 <- [52], 7 <- [0; 0] |} *)

  Eval vm_compute in List.nth 15 (fst c1) _.
  (* 16. *)
  Definition s16_1 := Eval vm_compute in (step_checker s15_1 (List.nth 15 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s16_1.
  (* s16_1 = ({|  |} *)

  Eval vm_compute in List.nth 16 (fst c1) _.
  (* 17. *)
  Definition s17_1 := Eval vm_compute in (step_checker s16_1 (List.nth 16 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s17_1.
  (* s17_1 = ({|  |} *)

  Eval vm_compute in List.nth 17 (fst c1) _.
  (* 18. *)
  Definition s18_1 := Eval vm_compute in (step_checker s17_1 (List.nth 17 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s18_1.
  (* s18_1 = ({|  |} *)

  Eval vm_compute in List.nth 18 (fst c1) _.
  (* 19. *)
  Definition s19_1 := Eval vm_compute in (step_checker s18_1 (List.nth 18 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s19_1.
  (* s19_1 = ({|  |} *)

  Eval vm_compute in List.nth 19 (fst c1) _.
  (* 20. *)
  Definition s20_1 := Eval vm_compute in (step_checker s19_1 (List.nth 19 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s20_1.
  (* s20_1 = ({|  |} *)

  Eval vm_compute in List.nth 20 (fst c1) _.
  (* 21. *)
  Definition s21_1 := Eval vm_compute in (step_checker s20_1 (List.nth 20 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s21_1.
  (* s21_1 = ({|  |} *)

  Eval vm_compute in List.nth 21 (fst c1) _.
  (* 22. *)
  Definition s22_1 := Eval vm_compute in (step_checker s21_1 (List.nth 21 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s22_1.
  (* s22_1 = ({|  |} *)

  Eval vm_compute in List.nth 22 (fst c1) _.
  (* 23. *)
  Definition s23_1 := Eval vm_compute in (step_checker s22_1 (List.nth 22 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s23_1.
  (* s23_1 = ({|  |} *)

  Eval vm_compute in List.nth 23 (fst c1) _.
  (* 24. *)
  Definition s24_1 := Eval vm_compute in (step_checker s23_1 (List.nth 23 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s24_1.
  (* s24_1 = ({|  |} *)

  Eval vm_compute in List.nth 24 (fst c1) _.
  (* 25. *)
  Definition s25_1 := Eval vm_compute in (step_checker s24_1 (List.nth 24 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s25_1.
  (* s25_1 = ({|  |} *)

  Eval vm_compute in List.nth 25 (fst c1) _.
  (* 26. *)
  Definition s26_1 := Eval vm_compute in (step_checker s25_1 (List.nth 25 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s26_1.
  (* s26_1 = ({|  |} *)

  Eval vm_compute in List.nth 26 (fst c1) _.
  (* 27. *)
  Definition s27_1 := Eval vm_compute in (step_checker s26_1 (List.nth 26 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s27_1.
  (* s27_1 = ({|  |} *)

  Eval vm_compute in List.nth 27 (fst c1) _.
  (* 28. *)
  Definition s28_1 := Eval vm_compute in (step_checker s27_1 (List.nth 27 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s28_1.
  (* s28_1 = ({|  |} *)

  Eval vm_compute in List.nth 28 (fst c1) _.
  (* 29. *)
  Definition s29_1 := Eval vm_compute in (step_checker s28_1 (List.nth 28 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s29_1.
  (* s29_1 = ({|  |} *)

  Eval vm_compute in List.nth 29 (fst c1) _.
  (* 30. *)
  Definition s30_1 := Eval vm_compute in (step_checker s29_1 (List.nth 29 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s30_1.
  (* s30_1 = ({|  |} *)

  Eval vm_compute in List.nth 30 (fst c1) _.
  (* 31. *)
  Definition s31_1 := Eval vm_compute in (step_checker s30_1 (List.nth 30 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s31_1.
  (* s31_1 = ({|  |} *)

  Eval vm_compute in List.nth 31 (fst c1) _.
  (* 32. *)
  Definition s32_1 := Eval vm_compute in (step_checker s31_1 (List.nth 31 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s32_1.
  (* s32_1 = ({|  |} *)

  Eval vm_compute in List.nth 32 (fst c1) _.
  (* 33. *)
  Definition s33_1 := Eval vm_compute in (step_checker s32_1 (List.nth 32 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s33_1.
  (* s33_1 = ({|  |} *)

  Eval vm_compute in List.nth 33 (fst c1) _.
  (* 34. *)
  Definition s34_1 := Eval vm_compute in (step_checker s33_1 (List.nth 33 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s34_1.
  (* s34_1 = ({|  |} *)

  Eval vm_compute in List.nth 34 (fst c1) _.
  (* 35. *)
  Definition s35_1 := Eval vm_compute in (step_checker s34_1 (List.nth 34 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s35_1.
  (* s35_1 = ({|  |} *)

  Eval vm_compute in List.nth 35 (fst c1) _.
  (* 36. *)
  Definition s36_1 := Eval vm_compute in (step_checker s35_1 (List.nth 35 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s36_1.
  (* s36_1 = ({|  |} *)

  Eval vm_compute in List.nth 36 (fst c1) _.
  (* 37. *)
  Definition s37_1 := Eval vm_compute in (step_checker s36_1 (List.nth 36 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s37_1.
  (* s37_1 = ({|  |} *)

  Eval vm_compute in List.nth 37 (fst c1) _.
  (* 38. *)
  Definition s38_1 := Eval vm_compute in (step_checker s37_1 (List.nth 37 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s38_1.
  (* s38_1 = ({|  |} *)

  Eval vm_compute in List.nth 38 (fst c1) _.
  (* 39. *)
  Definition s39_1 := Eval vm_compute in (step_checker s38_1 (List.nth 38 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s39_1.
  (* s39_1 = ({|  |} *)

  Eval vm_compute in List.nth 39 (fst c1) _.
  (* 40. *)
  Definition s40_1 := Eval vm_compute in (step_checker s39_1 (List.nth 39 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s40_1.
  (* s40_1 = ({|  |} *)

  Eval vm_compute in List.nth 40 (fst c1) _.
  (* 41. *)
  Definition s41_1 := Eval vm_compute in (step_checker s40_1 (List.nth 40 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s41_1.
  (* s41_1 = ({|  |} *)

  Eval vm_compute in List.nth 41 (fst c1) _.
  (* 42. *)
  Definition s42_1 := Eval vm_compute in (step_checker s41_1 (List.nth 41 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s42_1.
  (* s42_1 = ({|  |} *)

  Eval vm_compute in List.nth 42 (fst c1) _.
  (* 43. *)
  Definition s43_1 := Eval vm_compute in (step_checker s42_1 (List.nth 42 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s43_1.
  (* s43_1 = ({|  |} *)

  Eval vm_compute in List.nth 43 (fst c1) _.
  (* 44. *)
  Definition s44_1 := Eval vm_compute in (step_checker s43_1 (List.nth 43 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s44_1.
  (* s44_1 = ({|  |} *)

  Eval vm_compute in List.nth 44 (fst c1) _.
  (* 45. *)
  Definition s45_1 := Eval vm_compute in (step_checker s44_1 (List.nth 44 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s45_1.
  (* s45_1 = ({|  |} *)

  Eval vm_compute in List.nth 45 (fst c1) _.
  (* 46. *)
  Definition s46_1 := Eval vm_compute in (step_checker s45_1 (List.nth 45 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s46_1.
  (* s46_1 = ({|  |} *)

  Eval vm_compute in List.nth 46 (fst c1) _.
  (* 47. *)
  Definition s47_1 := Eval vm_compute in (step_checker s46_1 (List.nth 46 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s47_1.
  (* s47_1 = ({|  |} *)

  Eval vm_compute in List.nth 47 (fst c1) _.
  (* 48. *)
  Definition s48_1 := Eval vm_compute in (step_checker s47_1 (List.nth 47 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s48_1.
  (* s48_1 = ({|  |} *)

  Eval vm_compute in List.nth 48 (fst c1) _.
  (* 49. *)
  Definition s49_1 := Eval vm_compute in (step_checker s48_1 (List.nth 48 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s49_1.
  (* s49_1 = ({|  |} *)

  Eval vm_compute in List.nth 49 (fst c1) _.
  (* 50. *)
  Definition s50_1 := Eval vm_compute in (step_checker s49_1 (List.nth 49 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s50_1.
  (* s50_1 = ({|  |} *)

  Eval vm_compute in List.nth 50 (fst c1) _.
  (* 51. *)
  Definition s51_1 := Eval vm_compute in (step_checker s50_1 (List.nth 50 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s51_1.
  (* s51_1 = ({|  |} *)

  Eval vm_compute in List.nth 51 (fst c1) _.
  (* 52. *)
  Definition s52_1 := Eval vm_compute in (step_checker s51_1 (List.nth 51 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s52_1.
  (* s52_1 = ({|  |} *)

  Eval vm_compute in List.nth 52 (fst c1) _.
  (* 53. *)
  Definition s53_1 := Eval vm_compute in (step_checker s52_1 (List.nth 52 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s53_1.
  (* s53_1 = ({|  |} *)

  Eval vm_compute in List.nth 53 (fst c1) _.
  (* 54. *)
  Definition s54_1 := Eval vm_compute in (step_checker s53_1 (List.nth 53 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s54_1.
  (* s54_1 = ({|  |} *)

  Eval vm_compute in List.nth 54 (fst c1) _.
  (* 55. *)
  Definition s55_1 := Eval vm_compute in (step_checker s54_1 (List.nth 54 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s55_1.
  (* s55_1 = ({|  |} *)

  Eval vm_compute in List.nth 55 (fst c1) _.
  (* 56. *)
  Definition s56_1 := Eval vm_compute in (step_checker s55_1 (List.nth 55 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s56_1.
  (* s56_1 = ({|  |} *)

  Eval vm_compute in List.nth 56 (fst c1) _.
  (* 57. *)
  Definition s57_1 := Eval vm_compute in (step_checker s56_1 (List.nth 56 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s57_1.
  (* s57_1 = ({|  |} *)

  Eval vm_compute in List.nth 57 (fst c1) _.
  (* 58. *)
  Definition s58_1 := Eval vm_compute in (step_checker s57_1 (List.nth 57 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s58_1.
  (* s58_1 = ({|  |} *)

  Eval vm_compute in List.nth 58 (fst c1) _.
  (* 59. *)
  Definition s59_1 := Eval vm_compute in (step_checker s58_1 (List.nth 58 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s59_1.
  (* s59_1 = ({|  |} *)

  Eval vm_compute in List.nth 59 (fst c1) _.
  (* 60. *)
  Definition s60_1 := Eval vm_compute in (step_checker s59_1 (List.nth 59 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s60_1.
  (* s60_1 = ({|  |} *)

  Eval vm_compute in List.nth 60 (fst c1) _.
  (* 61. *)
  Definition s61_1 := Eval vm_compute in (step_checker s60_1 (List.nth 60 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s61_1.
  (* s61_1 = ({|  |} *)

  Eval vm_compute in List.nth 61 (fst c1) _.
  (* 62. *)
  Definition s62_1 := Eval vm_compute in (step_checker s61_1 (List.nth 61 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s62_1.
  (* s62_1 = ({|  |} *)

  Eval vm_compute in List.nth 62 (fst c1) _.
  (* 63. *)
  Definition s63_1 := Eval vm_compute in (step_checker s62_1 (List.nth 62 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s63_1.
  (* s63_1 = ({|  |} *)

  Eval vm_compute in List.nth 63 (fst c1) _.
  (* 64. *)
  Definition s64_1 := Eval vm_compute in (step_checker s63_1 (List.nth 63 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s64_1.
  (* s64_1 = ({|  |} *)

  Eval vm_compute in List.nth 64 (fst c1) _.
  (* 65. *)
  Definition s65_1 := Eval vm_compute in (step_checker s64_1 (List.nth 64 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s65_1.
  (* s65_1 = ({|  |} *)

  Eval vm_compute in List.nth 65 (fst c1) _.
  (* 66. *)
  Definition s66_1 := Eval vm_compute in (step_checker s65_1 (List.nth 65 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s66_1.
  (* s66_1 = ({|  |} *)

  Eval vm_compute in List.nth 66 (fst c1) _.
  (* 67. *)
  Definition s67_1 := Eval vm_compute in (step_checker s66_1 (List.nth 66 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s67_1.
  (* s67_1 = ({|  |} *)

  Eval vm_compute in List.nth 67 (fst c1) _.
  (* 68. *)
  Definition s68_1 := Eval vm_compute in (step_checker s67_1 (List.nth 67 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s68_1.
  (* s68_1 = ({|  |} *)

  Eval vm_compute in List.nth 68 (fst c1) _.
  (* 69. *)
  Definition s69_1 := Eval vm_compute in (step_checker s68_1 (List.nth 68 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s69_1.
  (* s69_1 = ({|  |} *)

  Eval vm_compute in List.nth 69 (fst c1) _.
  (* 70. *)
  Definition s70_1 := Eval vm_compute in (step_checker s69_1 (List.nth 69 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s70_1.
  (* s70_1 = ({|  |} *)

  Eval vm_compute in List.nth 70 (fst c1) _.
  (* 71. *)
  Definition s71_1 := Eval vm_compute in (step_checker s70_1 (List.nth 70 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s71_1.
  (* s71_1 = ({|  |} *)

  Eval vm_compute in List.nth 71 (fst c1) _.
  (* 72. *)
  Definition s72_1 := Eval vm_compute in (step_checker s71_1 (List.nth 71 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s72_1.
  (* s72_1 = ({|  |} *)

  Eval vm_compute in List.nth 72 (fst c1) _.
  (* 73. *)
  Definition s73_1 := Eval vm_compute in (step_checker s72_1 (List.nth 72 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s73_1.
  (* s73_1 = ({|  |} *)

  Eval vm_compute in List.nth 73 (fst c1) _.
  (* 74. *)
  Definition s74_1 := Eval vm_compute in (step_checker s73_1 (List.nth 73 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s74_1.
  (* s74_1 = ({|  |} *)

  Eval vm_compute in List.nth 74 (fst c1) _.
  (* 75. *)
  Definition s75_1 := Eval vm_compute in (step_checker s74_1 (List.nth 74 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s75_1.
  (* s75_1 = ({|  |} *)

  Eval vm_compute in List.nth 75 (fst c1) _.
  (* 76. *)
  Definition s76_1 := Eval vm_compute in (step_checker s75_1 (List.nth 75 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s76_1.
  (* s76_1 = ({|  |} *)

  Eval vm_compute in List.nth 76 (fst c1) _.
  (* 77. *)
  Definition s77_1 := Eval vm_compute in (step_checker s76_1 (List.nth 76 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s77_1.
  (* s77_1 = ({|  |} *)

  Eval vm_compute in List.nth 77 (fst c1) _.
  (* 78. *)
  Definition s78_1 := Eval vm_compute in (step_checker s77_1 (List.nth 77 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s78_1.
  (* s78_1 = ({|  |} *)

  Eval vm_compute in List.nth 78 (fst c1) _.
  (* 79. *)
  Definition s79_1 := Eval vm_compute in (step_checker s78_1 (List.nth 78 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s79_1.
  (* s79_1 = ({|  |} *)

  Eval vm_compute in List.nth 79 (fst c1) _.
  (* 80. *)
  Definition s80_1 := Eval vm_compute in (step_checker s79_1 (List.nth 79 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s80_1.
  (* s80_1 = ({|  |} *)

  Eval vm_compute in List.nth 80 (fst c1) _.
  (* 81. *)
  Definition s81_1 := Eval vm_compute in (step_checker s80_1 (List.nth 80 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s81_1.
  (* s81_1 = ({|  |} *)

  Eval vm_compute in List.nth 81 (fst c1) _.
  (* 82. *)
  Definition s82_1 := Eval vm_compute in (step_checker s81_1 (List.nth 81 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s82_1.
  (* s82_1 = ({|  |} *)

  Eval vm_compute in List.nth 82 (fst c1) _.
  (* 83. *)
  Definition s83_1 := Eval vm_compute in (step_checker s82_1 (List.nth 82 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s83_1.
  (* s83_1 = ({|  |} *)

  Eval vm_compute in List.nth 83 (fst c1) _.
  (* 84. *)
  Definition s84_1 := Eval vm_compute in (step_checker s83_1 (List.nth 83 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s84_1.
  (* s84_1 = ({|  |} *)

  Eval vm_compute in List.nth 84 (fst c1) _.
  (* 85. *)
  Definition s85_1 := Eval vm_compute in (step_checker s84_1 (List.nth 84 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s85_1.
  (* s85_1 = ({|  |} *)

  Eval vm_compute in List.nth 85 (fst c1) _.
  (* 86. *)
  Definition s86_1 := Eval vm_compute in (step_checker s85_1 (List.nth 85 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s86_1.
  (* s86_1 = ({|  |} *)

  Eval vm_compute in List.nth 86 (fst c1) _.
  (* 87. *)
  Definition s87_1 := Eval vm_compute in (step_checker s86_1 (List.nth 86 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s87_1.
  (* s87_1 = ({|  |} *)

  Eval vm_compute in List.nth 87 (fst c1) _.
  (* 88. *)
  Definition s88_1 := Eval vm_compute in (step_checker s87_1 (List.nth 87 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s88_1.
  (* s88_1 = ({|  |} *)

  Eval vm_compute in List.nth 88 (fst c1) _.
  (* 89. *)
  Definition s89_1 := Eval vm_compute in (step_checker s88_1 (List.nth 88 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s89_1.
  (* s89_1 = ({|  |} *)

  Eval vm_compute in List.nth 89 (fst c1) _.
  (* 90. *)
  Definition s90_1 := Eval vm_compute in (step_checker s89_1 (List.nth 89 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s90_1.
  (* s90_1 = ({|  |} *)

  Eval vm_compute in List.nth 90 (fst c1) _.
  (* 91. *)
  Definition s91_1 := Eval vm_compute in (step_checker s90_1 (List.nth 90 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s91_1.
  (* s91_1 = ({|  |} *)

  Eval vm_compute in List.nth 91 (fst c1) _.
  (* 92. *)
  Definition s92_1 := Eval vm_compute in (step_checker s91_1 (List.nth 91 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s92_1.
  (* s92_1 = ({|  |} *)

  Eval vm_compute in List.nth 92 (fst c1) _.
  (* 93. *)
  Definition s93_1 := Eval vm_compute in (step_checker s92_1 (List.nth 92 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s93_1.
  (* s93_1 = ({|  |} *)

  Eval vm_compute in List.nth 93 (fst c1) _.
  (* 94. *)
  Definition s94_1 := Eval vm_compute in (step_checker s93_1 (List.nth 93 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s94_1.
  (* s94_1 = ({|  |} *)

  Eval vm_compute in List.nth 94 (fst c1) _.
  (* 95. *)
  Definition s95_1 := Eval vm_compute in (step_checker s94_1 (List.nth 94 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s95_1.
  (* s95_1 = ({|  |} *)

  Eval vm_compute in List.nth 95 (fst c1) _.
  (* 96. *)
  Definition s96_1 := Eval vm_compute in (step_checker s95_1 (List.nth 95 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s96_1.
  (* s96_1 = ({|  |} *)

  Eval vm_compute in List.nth 96 (fst c1) _.
  (* 97. *)
  Definition s97_1 := Eval vm_compute in (step_checker s96_1 (List.nth 96 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s97_1.
  (* s97_1 = ({|  |} *)

  Eval vm_compute in List.nth 97 (fst c1) _.
  (* 98. *)
  Definition s98_1 := Eval vm_compute in (step_checker s97_1 (List.nth 97 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s98_1.
  (* s98_1 = ({|  |} *)

  Eval vm_compute in List.nth 98 (fst c1) _.
  (* 99. *)
  Definition s99_1 := Eval vm_compute in (step_checker s98_1 (List.nth 98 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s99_1.
  (* s99_1 = ({|  |} *)

  Eval vm_compute in List.nth 99 (fst c1) _.
  (* 100. *)
  Definition s100_1 := Eval vm_compute in (step_checker s99_1 (List.nth 99 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s100_1.
  (* s100_1 = ({|  |} *)

  Eval vm_compute in List.nth 100 (fst c1) _.
  (* 101. *)
  Definition s101_1 := Eval vm_compute in (step_checker s100_1 (List.nth 100 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s101_1.
  (* s101_1 = ({|  |} *)

  Eval vm_compute in List.nth 101 (fst c1) _.
  (* 102. *)
  Definition s102_1 := Eval vm_compute in (step_checker s101_1 (List.nth 101 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s102_1.
  (* s102_1 = ({|  |} *)

  Eval vm_compute in List.nth 102 (fst c1) _.
  (* 103. *)
  Definition s103_1 := Eval vm_compute in (step_checker s102_1 (List.nth 102 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s103_1.
  (* s103_1 = ({|  |} *)

  Eval vm_compute in List.nth 103 (fst c1) _.
  (* 104. *)
  Definition s104_1 := Eval vm_compute in (step_checker s103_1 (List.nth 103 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s104_1.
  (* s104_1 = ({|  |} *)

  Eval vm_compute in List.nth 104 (fst c1) _.
  (* 105. *)
  Definition s105_1 := Eval vm_compute in (step_checker s104_1 (List.nth 104 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s105_1.
  (* s105_1 = ({|  |} *)

  Eval vm_compute in List.nth 105 (fst c1) _.
  (* 106. *)
  Definition s106_1 := Eval vm_compute in (step_checker s105_1 (List.nth 105 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s106_1.
  (* s106_1 = ({|  |} *)

  Eval vm_compute in List.nth 106 (fst c1) _.
  (* 107. *)
  Definition s107_1 := Eval vm_compute in (step_checker s106_1 (List.nth 106 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s107_1.
  (* s107_1 = ({|  |} *)

  Eval vm_compute in List.nth 107 (fst c1) _.
  (* 108. *)
  Definition s108_1 := Eval vm_compute in (step_checker s107_1 (List.nth 107 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s108_1.
  (* s108_1 = ({|  |} *)

  Eval vm_compute in List.nth 108 (fst c1) _.
  (* 109. *)
  Definition s109_1 := Eval vm_compute in (step_checker s108_1 (List.nth 108 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s109_1.
  (* s109_1 = ({|  |} *)

  Eval vm_compute in List.nth 109 (fst c1) _.
  (* 110. *)
  Definition s110_1 := Eval vm_compute in (step_checker s109_1 (List.nth 109 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s110_1.
  (* s110_1 = ({|  |} *)

  Eval vm_compute in List.nth 110 (fst c1) _.
  (* 111. *)
  Definition s111_1 := Eval vm_compute in (step_checker s110_1 (List.nth 110 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s111_1.
  (* s111_1 = ({|  |} *)

  Eval vm_compute in List.nth 111 (fst c1) _.
  (* 112. *)
  Definition s112_1 := Eval vm_compute in (step_checker s111_1 (List.nth 111 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s112_1.
  (* s112_1 = ({|  |} *)

  Eval vm_compute in List.nth 112 (fst c1) _.
  (* 113. *)
  Definition s113_1 := Eval vm_compute in (step_checker s112_1 (List.nth 112 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s113_1.
  (* s113_1 = ({|  |} *)

  Eval vm_compute in List.nth 113 (fst c1) _.
  (* 114. *)
  Definition s114_1 := Eval vm_compute in (step_checker s113_1 (List.nth 113 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s114_1.
  (* s114_1 = ({|  |} *)

  Eval vm_compute in List.nth 114 (fst c1) _.
  (* 115. *)
  Definition s115_1 := Eval vm_compute in (step_checker s114_1 (List.nth 114 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s115_1.
  (* s115_1 = ({|  |} *)

  Eval vm_compute in List.nth 115 (fst c1) _.
  (* 116. *)
  Definition s116_1 := Eval vm_compute in (step_checker s115_1 (List.nth 115 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s116_1.
  (* s116_1 = ({|  |} *)

  Eval vm_compute in List.nth 116 (fst c1) _.
  (* 117. *)
  Definition s117_1 := Eval vm_compute in (step_checker s116_1 (List.nth 116 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s117_1.
  (* s117_1 = ({|  |} *)

  Eval vm_compute in List.nth 117 (fst c1) _.
  (* 118. *)
  Definition s118_1 := Eval vm_compute in (step_checker s117_1 (List.nth 117 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s118_1.
  (* s118_1 = ({|  |} *)

  Eval vm_compute in List.nth 118 (fst c1) _.
  (* 119. *)
  Definition s119_1 := Eval vm_compute in (step_checker s118_1 (List.nth 118 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s119_1.
  (* s119_1 = ({|  |} *)

  Eval vm_compute in List.nth 119 (fst c1) _.
  (* 120. *)
  Definition s120_1 := Eval vm_compute in (step_checker s119_1 (List.nth 119 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s120_1.
  (* s120_1 = ({|  |} *)

  Eval vm_compute in List.nth 120 (fst c1) _.
  (* 121. *)
  Definition s121_1 := Eval vm_compute in (step_checker s120_1 (List.nth 120 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s121_1.
  (* s121_1 = ({|  |} *)

  Eval vm_compute in List.nth 121 (fst c1) _.
  (* 122. *)
  Definition s122_1 := Eval vm_compute in (step_checker s121_1 (List.nth 121 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s122_1.
  (* s122_1 = ({|  |} *)

  Eval vm_compute in List.nth 122 (fst c1) _.
  (* 123. *)
  Definition s123_1 := Eval vm_compute in (step_checker s122_1 (List.nth 122 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s123_1.
  (* s123_1 = ({|  |} *)

  Eval vm_compute in List.nth 123 (fst c1) _.
  (* 124. *)
  Definition s124_1 := Eval vm_compute in (step_checker s123_1 (List.nth 123 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s124_1.
  (* s124_1 = ({|  |} *)

  Eval vm_compute in List.nth 124 (fst c1) _.
  (* 125. *)
  Definition s125_1 := Eval vm_compute in (step_checker s124_1 (List.nth 124 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s125_1.
  (* s125_1 = ({|  |} *)

  Eval vm_compute in List.nth 125 (fst c1) _.
  (* 126. *)
  Definition s126_1 := Eval vm_compute in (step_checker s125_1 (List.nth 125 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s126_1.
  (* s126_1 = ({|  |} *)

  Eval vm_compute in List.nth 126 (fst c1) _.
  (* 127. *)
  Definition s127_1 := Eval vm_compute in (step_checker s126_1 (List.nth 126 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s127_1.
  (* s127_1 = ({|  |} *)

  Eval vm_compute in List.nth 127 (fst c1) _.
  (* 128. *)
  Definition s128_1 := Eval vm_compute in (step_checker s127_1 (List.nth 127 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s128_1.
  (* s128_1 = ({|  |} *)

  Eval vm_compute in List.nth 128 (fst c1) _.
  (* 129. *)
  Definition s129_1 := Eval vm_compute in (step_checker s128_1 (List.nth 128 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s129_1.
  (* s129_1 = ({|  |} *)

  Eval vm_compute in List.nth 129 (fst c1) _.
  (* 130. *)
  Definition s130_1 := Eval vm_compute in (step_checker s129_1 (List.nth 129 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s130_1.
  (* s130_1 = ({|  |} *)

  Eval vm_compute in List.nth 130 (fst c1) _.
  (* 131. *)
  Definition s131_1 := Eval vm_compute in (step_checker s130_1 (List.nth 130 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s131_1.
  (* s131_1 = ({|  |} *)

  Eval vm_compute in List.nth 131 (fst c1) _.
  (* 132. *)
  Definition s132_1 := Eval vm_compute in (step_checker s131_1 (List.nth 131 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s132_1.
  (* s132_1 = ({|  |} *)

  Eval vm_compute in List.nth 132 (fst c1) _.
  (* 133. *)
  Definition s133_1 := Eval vm_compute in (step_checker s132_1 (List.nth 132 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s133_1.
  (* s133_1 = ({|  |} *)

  Eval vm_compute in List.nth 133 (fst c1) _.
  (* 134. *)
  Definition s134_1 := Eval vm_compute in (step_checker s133_1 (List.nth 133 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s134_1.
  (* s134_1 = ({|  |} *)

  Eval vm_compute in List.nth 134 (fst c1) _.
  (* 135. *)
  Definition s135_1 := Eval vm_compute in (step_checker s134_1 (List.nth 134 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s135_1.
  (* s135_1 = ({|  |} *)

  Eval vm_compute in List.nth 135 (fst c1) _.
  (* 136. *)
  Definition s136_1 := Eval vm_compute in (step_checker s135_1 (List.nth 135 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s136_1.
  (* s136_1 = ({|  |} *)

  Eval vm_compute in List.nth 136 (fst c1) _.
  (* 137. *)
  Definition s137_1 := Eval vm_compute in (step_checker s136_1 (List.nth 136 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s137_1.
  (* s137_1 = ({|  |} *)

  Eval vm_compute in List.nth 137 (fst c1) _.
  (* 138. *)
  Definition s138_1 := Eval vm_compute in (step_checker s137_1 (List.nth 137 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s138_1.
  (* s138_1 = ({|  |} *)

  Eval vm_compute in List.nth 138 (fst c1) _.
  (* 139. *)
  Definition s139_1 := Eval vm_compute in (step_checker s138_1 (List.nth 138 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s139_1.
  (* s139_1 = ({|  |} *)

  Eval vm_compute in List.nth 139 (fst c1) _.
  (* 140. *)
  Definition s140_1 := Eval vm_compute in (step_checker s139_1 (List.nth 139 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s140_1.
  (* s140_1 = ({|  |} *)

  Eval vm_compute in List.nth 140 (fst c1) _.
  (* 141. *)
  Definition s141_1 := Eval vm_compute in (step_checker s140_1 (List.nth 140 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s141_1.
  (* s141_1 = ({|  |} *)

  Eval vm_compute in List.nth 141 (fst c1) _.
  (* 142. *)
  Definition s142_1 := Eval vm_compute in (step_checker s141_1 (List.nth 141 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s142_1.
  (* s142_1 = ({|  |} *)

  Eval vm_compute in List.nth 142 (fst c1) _.
  (* 143. *)
  Definition s143_1 := Eval vm_compute in (step_checker s142_1 (List.nth 142 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s143_1.
  (* s143_1 = ({|  |} *)

  Eval vm_compute in List.nth 143 (fst c1) _.
  (* 144. *)
  Definition s144_1 := Eval vm_compute in (step_checker s143_1 (List.nth 143 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s144_1.
  (* s144_1 = ({|  |} *)

  Eval vm_compute in List.nth 144 (fst c1) _.
  (* 145. *)
  Definition s145_1 := Eval vm_compute in (step_checker s144_1 (List.nth 144 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s145_1.
  (* s145_1 = ({|  |} *)

  Eval vm_compute in List.nth 145 (fst c1) _.
  (* 146. *)
  Definition s146_1 := Eval vm_compute in (step_checker s145_1 (List.nth 145 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s146_1.
  (* s146_1 = ({|  |} *)

  Eval vm_compute in List.nth 146 (fst c1) _.
  (* 147. *)
  Definition s147_1 := Eval vm_compute in (step_checker s146_1 (List.nth 146 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s147_1.
  (* s147_1 = ({|  |} *)

  Eval vm_compute in List.nth 147 (fst c1) _.
  (* 148. *)
  Definition s148_1 := Eval vm_compute in (step_checker s147_1 (List.nth 147 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s148_1.
  (* s148_1 = ({|  |} *)

  Eval vm_compute in List.nth 148 (fst c1) _.
  (* 149. *)
  Definition s149_1 := Eval vm_compute in (step_checker s148_1 (List.nth 148 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s149_1.
  (* s149_1 = ({|  |} *)

  Eval vm_compute in List.nth 149 (fst c1) _.
  (* 150. *)
  Definition s150_1 := Eval vm_compute in (step_checker s149_1 (List.nth 149 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s150_1.
  (* s150_1 = ({|  |} *)

  Eval vm_compute in List.nth 150 (fst c1) _.
  (* 151. *)
  Definition s151_1 := Eval vm_compute in (step_checker s150_1 (List.nth 150 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s151_1.
  (* s151_1 = ({|  |} *)

  Eval vm_compute in List.nth 151 (fst c1) _.
  (* 152. *)
  Definition s152_1 := Eval vm_compute in (step_checker s151_1 (List.nth 151 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s152_1.
  (* s152_1 = ({|  |} *)

  Eval vm_compute in List.nth 152 (fst c1) _.
  (* 153. *)
  Definition s153_1 := Eval vm_compute in (step_checker s152_1 (List.nth 152 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s153_1.
  (* s153_1 = ({|  |} *)

  Eval vm_compute in List.nth 153 (fst c1) _.
  (* 154. *)
  Definition s154_1 := Eval vm_compute in (step_checker s153_1 (List.nth 153 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s154_1.
  (* s154_1 = ({|  |} *)

  Eval vm_compute in List.nth 154 (fst c1) _.
  (* 155. *)
  Definition s155_1 := Eval vm_compute in (step_checker s154_1 (List.nth 154 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s155_1.
  (* s155_1 = ({|  |} *)

  Eval vm_compute in List.nth 155 (fst c1) _.
  (* 156. *)
  Definition s156_1 := Eval vm_compute in (step_checker s155_1 (List.nth 155 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s156_1.
  (* s156_1 = ({|  |} *)

  Eval vm_compute in List.nth 156 (fst c1) _.
  (* 157. *)
  Definition s157_1 := Eval vm_compute in (step_checker s156_1 (List.nth 156 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s157_1.
  (* s157_1 = ({|  |} *)

  Eval vm_compute in List.nth 157 (fst c1) _.
  (* 158. *)
  Definition s158_1 := Eval vm_compute in (step_checker s157_1 (List.nth 157 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s158_1.
  (* s158_1 = ({|  |} *)

  Eval vm_compute in List.nth 158 (fst c1) _.
  (* 159. *)
  Definition s159_1 := Eval vm_compute in (step_checker s158_1 (List.nth 158 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s159_1.
  (* s159_1 = ({|  |} *)

  Eval vm_compute in List.nth 159 (fst c1) _.
  (* 160. *)
  Definition s160_1 := Eval vm_compute in (step_checker s159_1 (List.nth 159 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s160_1.
  (* s160_1 = ({|  |} *)

  Eval vm_compute in List.nth 160 (fst c1) _.
  (* 161. *)
  Definition s161_1 := Eval vm_compute in (step_checker s160_1 (List.nth 160 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s161_1.
  (* s161_1 = ({|  |} *)

  Eval vm_compute in List.nth 161 (fst c1) _.
  (* 162. *)
  Definition s162_1 := Eval vm_compute in (step_checker s161_1 (List.nth 161 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s162_1.
  (* s162_1 = ({|  |} *)

  Eval vm_compute in List.nth 162 (fst c1) _.
  (* 163. *)
  Definition s163_1 := Eval vm_compute in (step_checker s162_1 (List.nth 162 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s163_1.
  (* s163_1 = ({|  |} *)

  Eval vm_compute in List.nth 163 (fst c1) _.
  (* 164. *)
  Definition s164_1 := Eval vm_compute in (step_checker s163_1 (List.nth 163 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s164_1.
  (* s164_1 = ({|  |} *)

  Eval vm_compute in List.nth 164 (fst c1) _.
  (* 165. *)
  Definition s165_1 := Eval vm_compute in (step_checker s164_1 (List.nth 164 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s165_1.
  (* s165_1 = ({|  |} *)

  Eval vm_compute in List.nth 165 (fst c1) _.
  (* 166. *)
  Definition s166_1 := Eval vm_compute in (step_checker s165_1 (List.nth 165 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s166_1.
  (* s166_1 = ({|  |} *)

  Eval vm_compute in List.nth 166 (fst c1) _.
  (* 167. *)
  Definition s167_1 := Eval vm_compute in (step_checker s166_1 (List.nth 166 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s167_1.
  (* s167_1 = ({|  |} *)

  Eval vm_compute in List.nth 167 (fst c1) _.
  (* 168. *)
  Definition s168_1 := Eval vm_compute in (step_checker s167_1 (List.nth 167 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s168_1.
  (* s168_1 = ({|  |} *)

  Eval vm_compute in List.nth 168 (fst c1) _.
  (* 169. *)
  Definition s169_1 := Eval vm_compute in (step_checker s168_1 (List.nth 168 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s169_1.
  (* s169_1 = ({|  |} *)

  Eval vm_compute in List.nth 169 (fst c1) _.
  (* 170. *)
  Definition s170_1 := Eval vm_compute in (step_checker s169_1 (List.nth 169 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s170_1.
  (* s170_1 = ({|  |} *)

  Eval vm_compute in List.nth 170 (fst c1) _.
  (* 171. *)
  Definition s171_1 := Eval vm_compute in (step_checker s170_1 (List.nth 170 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s171_1.
  (* s171_1 = ({|  |} *)

  Eval vm_compute in List.nth 171 (fst c1) _.
  (* 172. *)
  Definition s172_1 := Eval vm_compute in (step_checker s171_1 (List.nth 171 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s172_1.
  (* s172_1 = ({|  |} *)

  Eval vm_compute in List.nth 172 (fst c1) _.
  (* 173. *)
  Definition s173_1 := Eval vm_compute in (step_checker s172_1 (List.nth 172 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s173_1.
  (* s173_1 = ({|  |} *)

  Eval vm_compute in List.nth 173 (fst c1) _.
  (* 174. *)
  Definition s174_1 := Eval vm_compute in (step_checker s173_1 (List.nth 173 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s174_1.
  (* s174_1 = ({|  |} *)

  Eval vm_compute in List.nth 174 (fst c1) _.
  (* 175. *)
  Definition s175_1 := Eval vm_compute in (step_checker s174_1 (List.nth 174 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s175_1.
  (* s175_1 = ({|  |} *)

  Eval vm_compute in List.nth 175 (fst c1) _.
  (* 176. *)
  Definition s176_1 := Eval vm_compute in (step_checker s175_1 (List.nth 175 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s176_1.
  (* s176_1 = ({|  |} *)

  Eval vm_compute in List.nth 176 (fst c1) _.
  (* 177. *)
  Definition s177_1 := Eval vm_compute in (step_checker s176_1 (List.nth 176 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s177_1.
  (* s177_1 = ({|  |} *)

  Eval vm_compute in List.nth 177 (fst c1) _.
  (* 178. *)
  Definition s178_1 := Eval vm_compute in (step_checker s177_1 (List.nth 177 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s178_1.
  (* s178_1 = ({|  |} *)

  Eval vm_compute in List.nth 178 (fst c1) _.
  (* 179. *)
  Definition s179_1 := Eval vm_compute in (step_checker s178_1 (List.nth 178 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s179_1.
  (* s179_1 = ({|  |} *)

  Eval vm_compute in List.nth 179 (fst c1) _.
  (* 180. *)
  Definition s180_1 := Eval vm_compute in (step_checker s179_1 (List.nth 179 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s180_1.
  (* s180_1 = ({|  |} *)

  Eval vm_compute in List.nth 180 (fst c1) _.
  (* 181. *)
  Definition s181_1 := Eval vm_compute in (step_checker s180_1 (List.nth 180 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s181_1.
  (* s181_1 = ({|  |} *)

  Eval vm_compute in List.nth 181 (fst c1) _.
  (* 182. *)
  Definition s182_1 := Eval vm_compute in (step_checker s181_1 (List.nth 181 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s182_1.
  (* s182_1 = ({|  |} *)

  Eval vm_compute in List.nth 182 (fst c1) _.
  (* 183. *)
  Definition s183_1 := Eval vm_compute in (step_checker s182_1 (List.nth 182 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s183_1.
  (* s183_1 = ({|  |} *)

  Eval vm_compute in List.nth 183 (fst c1) _.
  (* 184. *)
  Definition s184_1 := Eval vm_compute in (step_checker s183_1 (List.nth 183 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s184_1.
  (* s184_1 = ({|  |} *)

  Eval vm_compute in List.nth 184 (fst c1) _.
  (* 185. *)
  Definition s185_1 := Eval vm_compute in (step_checker s184_1 (List.nth 184 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s185_1.
  (* s185_1 = ({|  |} *)

  Eval vm_compute in List.nth 185 (fst c1) _.
  (* 186. *)
  Definition s186_1 := Eval vm_compute in (step_checker s185_1 (List.nth 185 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s186_1.
  (* s186_1 = ({|  |} *)

  Eval vm_compute in List.nth 186 (fst c1) _.
  (* 187. *)
  Definition s187_1 := Eval vm_compute in (step_checker s186_1 (List.nth 186 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s187_1.
  (* s187_1 = ({|  |} *)

  Eval vm_compute in List.nth 187 (fst c1) _.
  (* 188. *)
  Definition s188_1 := Eval vm_compute in (step_checker s187_1 (List.nth 187 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s188_1.
  (* s188_1 = ({|  |} *)

  Eval vm_compute in List.nth 188 (fst c1) _.
  (* 189. *)
  Definition s189_1 := Eval vm_compute in (step_checker s188_1 (List.nth 188 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s189_1.
  (* s189_1 = ({|  |} *)

  Eval vm_compute in List.nth 189 (fst c1) _.
  (* 190. *)
  Definition s190_1 := Eval vm_compute in (step_checker s189_1 (List.nth 189 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s190_1.
  (* s190_1 = ({|  |} *)

  Eval vm_compute in List.nth 190 (fst c1) _.
  (* 191. *)
  Definition s191_1 := Eval vm_compute in (step_checker s190_1 (List.nth 190 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s191_1.
  (* s191_1 = ({|  |} *)

  Eval vm_compute in List.nth 191 (fst c1) _.
  (* 192. *)
  Definition s192_1 := Eval vm_compute in (step_checker s191_1 (List.nth 191 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s192_1.
  (* s192_1 = ({|  |} *)

  Eval vm_compute in List.nth 192 (fst c1) _.
  (* 193. *)
  Definition s193_1 := Eval vm_compute in (step_checker s192_1 (List.nth 192 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s193_1.
  (* s193_1 = ({|  |} *)

  Eval vm_compute in List.nth 193 (fst c1) _.
  (* 194. *)
  Definition s194_1 := Eval vm_compute in (step_checker s193_1 (List.nth 193 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s194_1.
  (* s194_1 = ({|  |} *)

  Eval vm_compute in List.nth 194 (fst c1) _.
  (* 195. *)
  Definition s195_1 := Eval vm_compute in (step_checker s194_1 (List.nth 194 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s195_1.
  (* s195_1 = ({|  |} *)

  Eval vm_compute in List.nth 195 (fst c1) _.
  (* 196. *)
  Definition s196_1 := Eval vm_compute in (step_checker s195_1 (List.nth 195 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s196_1.
  (* s196_1 = ({|  |} *)

  Eval vm_compute in List.nth 196 (fst c1) _.
  (* 197. *)
  Definition s197_1 := Eval vm_compute in (step_checker s196_1 (List.nth 196 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s197_1.
  (* s197_1 = ({|  |} *)

  Eval vm_compute in List.nth 197 (fst c1) _.
  (* 198. *)
  Definition s198_1 := Eval vm_compute in (step_checker s197_1 (List.nth 197 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s198_1.
  (* s198_1 = ({|  |} *)

  Eval vm_compute in List.nth 198 (fst c1) _.
  (* 199. *)
  Definition s199_1 := Eval vm_compute in (step_checker s198_1 (List.nth 198 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s199_1.
  (* s199_1 = ({|  |} *)

  Eval vm_compute in List.nth 199 (fst c1) _.
  (* 200. *)
  Definition s200_1 := Eval vm_compute in (step_checker s199_1 (List.nth 199 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s200_1.
  (* s200_1 = ({|  |} *)

  Eval vm_compute in List.nth 200 (fst c1) _.
  (* 201. *)
  Definition s201_1 := Eval vm_compute in (step_checker s200_1 (List.nth 200 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s201_1.
  (* s201_1 = ({|  |} *)

  Eval vm_compute in List.nth 201 (fst c1) _.
  (* 202. *)
  Definition s202_1 := Eval vm_compute in (step_checker s201_1 (List.nth 201 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s202_1.
  (* s202_1 = ({|  |} *)

  Eval vm_compute in List.nth 202 (fst c1) _.
  (* 203. *)
  Definition s203_1 := Eval vm_compute in (step_checker s202_1 (List.nth 202 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s203_1.
  (* s203_1 = ({|  |} *)

  Eval vm_compute in List.nth 203 (fst c1) _.
  (* 204. *)
  Definition s204_1 := Eval vm_compute in (step_checker s203_1 (List.nth 203 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s204_1.
  (* s204_1 = ({|  |} *)

  Eval vm_compute in List.nth 204 (fst c1) _.
  (* 205. *)
  Definition s205_1 := Eval vm_compute in (step_checker s204_1 (List.nth 204 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s205_1.
  (* s205_1 = ({|  |} *)

  Eval vm_compute in List.nth 205 (fst c1) _.
  (* 206. *)
  Definition s206_1 := Eval vm_compute in (step_checker s205_1 (List.nth 205 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s206_1.
  (* s206_1 = ({|  |} *)

  Eval vm_compute in List.nth 206 (fst c1) _.
  (* 207. *)
  Definition s207_1 := Eval vm_compute in (step_checker s206_1 (List.nth 206 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s207_1.
  (* s207_1 = ({|  |} *)

  Eval vm_compute in List.nth 207 (fst c1) _.
  (* 208. *)
  Definition s208_1 := Eval vm_compute in (step_checker s207_1 (List.nth 207 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s208_1.
  (* s208_1 = ({|  |} *)

  Eval vm_compute in List.nth 208 (fst c1) _.
  (* 209. *)
  Definition s209_1 := Eval vm_compute in (step_checker s208_1 (List.nth 208 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s209_1.
  (* s209_1 = ({|  |} *)

  Eval vm_compute in List.nth 209 (fst c1) _.
  (* 210. *)
  Definition s210_1 := Eval vm_compute in (step_checker s209_1 (List.nth 209 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s210_1.
  (* s210_1 = ({|  |} *)

  Eval vm_compute in List.nth 210 (fst c1) _.
  (* 211. *)
  Definition s211_1 := Eval vm_compute in (step_checker s210_1 (List.nth 210 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s211_1.
  (* s211_1 = ({|  |} *)

  Eval vm_compute in List.nth 211 (fst c1) _.
  (* 212. *)
  Definition s212_1 := Eval vm_compute in (step_checker s211_1 (List.nth 211 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s212_1.
  (* s212_1 = ({|  |} *)

  Eval vm_compute in List.nth 212 (fst c1) _.
  (* 213. *)
  Definition s213_1 := Eval vm_compute in (step_checker s212_1 (List.nth 212 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s213_1.
  (* s213_1 = ({|  |} *)

  Eval vm_compute in List.nth 213 (fst c1) _.
  (* 214. *)
  Definition s214_1 := Eval vm_compute in (step_checker s213_1 (List.nth 213 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s214_1.
  (* s214_1 = ({|  |} *)

  Eval vm_compute in List.nth 214 (fst c1) _.
  (* 215. *)
  Definition s215_1 := Eval vm_compute in (step_checker s214_1 (List.nth 214 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s215_1.
  (* s215_1 = ({|  |} *)

  Eval vm_compute in List.nth 215 (fst c1) _.
  (* 216. *)
  Definition s216_1 := Eval vm_compute in (step_checker s215_1 (List.nth 215 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s216_1.
  (* s216_1 = ({|  |} *)

  Eval vm_compute in List.nth 216 (fst c1) _.
  (* 217. *)
  Definition s217_1 := Eval vm_compute in (step_checker s216_1 (List.nth 216 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s217_1.
  (* s217_1 = ({|  |} *)

  Eval vm_compute in List.nth 217 (fst c1) _.
  (* 218. *)
  Definition s218_1 := Eval vm_compute in (step_checker s217_1 (List.nth 217 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s218_1.
  (* s218_1 = ({|  |} *)

  Eval vm_compute in List.nth 218 (fst c1) _.
  (* 219. *)
  Definition s219_1 := Eval vm_compute in (step_checker s218_1 (List.nth 218 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s219_1.
  (* s219_1 = ({|  |} *)

  Eval vm_compute in List.nth 219 (fst c1) _.
  (* 220. *)
  Definition s220_1 := Eval vm_compute in (step_checker s219_1 (List.nth 219 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s220_1.
  (* s220_1 = ({|  |} *)

  Eval vm_compute in List.nth 220 (fst c1) _.
  (* 221. *)
  Definition s221_1 := Eval vm_compute in (step_checker s220_1 (List.nth 220 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s221_1.
  (* s221_1 = ({|  |} *)

  Eval vm_compute in List.nth 221 (fst c1) _.
  (* 222. *)
  Definition s222_1 := Eval vm_compute in (step_checker s221_1 (List.nth 221 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s222_1.
  (* s222_1 = ({|  |} *)

  Eval vm_compute in List.nth 222 (fst c1) _.
  (* 223. *)
  Definition s223_1 := Eval vm_compute in (step_checker s222_1 (List.nth 222 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s223_1.
  (* s223_1 = ({|  |} *)

  Eval vm_compute in List.nth 223 (fst c1) _.
  (* 224. *)
  Definition s224_1 := Eval vm_compute in (step_checker s223_1 (List.nth 223 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s224_1.
  (* s224_1 = ({|  |} *)

  Eval vm_compute in List.nth 224 (fst c1) _.
  (* 225. *)
  Definition s225_1 := Eval vm_compute in (step_checker s224_1 (List.nth 224 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s225_1.
  (* s225_1 = ({|  |} *)

  Eval vm_compute in List.nth 225 (fst c1) _.
  (* 226. *)
  Definition s226_1 := Eval vm_compute in (step_checker s225_1 (List.nth 225 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s226_1.
  (* s226_1 = ({|  |} *)

  Eval vm_compute in List.nth 226 (fst c1) _.
  (* 227. *)
  Definition s227_1 := Eval vm_compute in (step_checker s226_1 (List.nth 226 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s227_1.
  (* s227_1 = ({|  |} *)

  Eval vm_compute in List.nth 227 (fst c1) _.
  (* 228. *)
  Definition s228_1 := Eval vm_compute in (step_checker s227_1 (List.nth 227 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s228_1.
  (* s228_1 = ({|  |} *)

  Eval vm_compute in List.nth 228 (fst c1) _.
  (* 229. *)
  Definition s229_1 := Eval vm_compute in (step_checker s228_1 (List.nth 228 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s229_1.
  (* s229_1 = ({|  |} *)

  Eval vm_compute in List.nth 229 (fst c1) _.
  (* 230. *)
  Definition s230_1 := Eval vm_compute in (step_checker s229_1 (List.nth 229 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s230_1.
  (* s230_1 = ({|  |} *)

  Eval vm_compute in List.nth 230 (fst c1) _.
  (* 231. *)
  Definition s231_1 := Eval vm_compute in (step_checker s230_1 (List.nth 230 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s231_1.
  (* s231_1 = ({|  |} *)

  Eval vm_compute in List.nth 231 (fst c1) _.
  (* 232. *)
  Definition s232_1 := Eval vm_compute in (step_checker s231_1 (List.nth 231 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s232_1.
  (* s232_1 = ({|  |} *)

  Eval vm_compute in List.nth 232 (fst c1) _.
  (* 233. *)
  Definition s233_1 := Eval vm_compute in (step_checker s232_1 (List.nth 232 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s233_1.
  (* s233_1 = ({|  |} *)

  Eval vm_compute in List.nth 233 (fst c1) _.
  (* 234. *)
  Definition s234_1 := Eval vm_compute in (step_checker s233_1 (List.nth 233 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s234_1.
  (* s234_1 = ({|  |} *)

  Eval vm_compute in List.nth 234 (fst c1) _.
  (* 235. *)
  Definition s235_1 := Eval vm_compute in (step_checker s234_1 (List.nth 234 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s235_1.
  (* s235_1 = ({|  |} *)

  Eval vm_compute in List.nth 235 (fst c1) _.
  (* 236. *)
  Definition s236_1 := Eval vm_compute in (step_checker s235_1 (List.nth 235 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s236_1.
  (* s236_1 = ({|  |} *)

  Eval vm_compute in List.nth 236 (fst c1) _.
  (* 237. *)
  Definition s237_1 := Eval vm_compute in (step_checker s236_1 (List.nth 236 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s237_1.
  (* s237_1 = ({|  |} *)

  Eval vm_compute in List.nth 237 (fst c1) _.
  (* 238. *)
  Definition s238_1 := Eval vm_compute in (step_checker s237_1 (List.nth 237 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s238_1.
  (* s238_1 = ({|  |} *)

  Eval vm_compute in List.nth 238 (fst c1) _.
  (* 239. *)
  Definition s239_1 := Eval vm_compute in (step_checker s238_1 (List.nth 238 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s239_1.
  (* s239_1 = ({|  |} *)

  Eval vm_compute in List.nth 239 (fst c1) _.
  (* 240. *)
  Definition s240_1 := Eval vm_compute in (step_checker s239_1 (List.nth 239 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s240_1.
  (* s240_1 = ({|  |} *)

  Eval vm_compute in List.nth 240 (fst c1) _.
  (* 241. *)
  Definition s241_1 := Eval vm_compute in (step_checker s240_1 (List.nth 240 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s241_1.
  (* s241_1 = ({|  |} *)

  Eval vm_compute in List.nth 241 (fst c1) _.
  (* 242. *)
  Definition s242_1 := Eval vm_compute in (step_checker s241_1 (List.nth 241 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s242_1.
  (* s242_1 = ({|  |} *)

  Eval vm_compute in List.nth 242 (fst c1) _.
  (* 243. *)
  Definition s243_1 := Eval vm_compute in (step_checker s242_1 (List.nth 242 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s243_1.
  (* s243_1 = ({|  |} *)

  Eval vm_compute in List.nth 243 (fst c1) _.
  (* 244. *)
  Definition s244_1 := Eval vm_compute in (step_checker s243_1 (List.nth 243 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s244_1.
  (* s244_1 = ({|  |} *)

  Eval vm_compute in List.nth 244 (fst c1) _.
  (* 245. *)
  Definition s245_1 := Eval vm_compute in (step_checker s244_1 (List.nth 244 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s245_1.
  (* s245_1 = ({|  |} *)

  Eval vm_compute in List.nth 245 (fst c1) _.
  (* 246. *)
  Definition s246_1 := Eval vm_compute in (step_checker s245_1 (List.nth 245 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s246_1.
  (* s246_1 = ({|  |} *)

  Eval vm_compute in List.nth 246 (fst c1) _.
  (* 247. *)
  Definition s247_1 := Eval vm_compute in (step_checker s246_1 (List.nth 246 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s247_1.
  (* s247_1 = ({|  |} *)

  Eval vm_compute in List.nth 247 (fst c1) _.
  (* 248. *)
  Definition s248_1 := Eval vm_compute in (step_checker s247_1 (List.nth 247 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s248_1.
  (* s248_1 = ({|  |} *)

  Eval vm_compute in List.nth 248 (fst c1) _.
  (* 249. *)
  Definition s249_1 := Eval vm_compute in (step_checker s248_1 (List.nth 248 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s249_1.
  (* s249_1 = ({|  |} *)

  Eval vm_compute in List.nth 249 (fst c1) _.
  (* 250. *)
  Definition s250_1 := Eval vm_compute in (step_checker s249_1 (List.nth 249 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s250_1.
  (* s250_1 = ({|  |} *)

  Eval vm_compute in List.nth 250 (fst c1) _.
  (* 251. *)
  Definition s251_1 := Eval vm_compute in (step_checker s250_1 (List.nth 250 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s251_1.
  (* s251_1 = ({|  |} *)

  Eval vm_compute in List.nth 251 (fst c1) _.
  (* 252. *)
  Definition s252_1 := Eval vm_compute in (step_checker s251_1 (List.nth 251 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s252_1.
  (* s252_1 = ({|  |} *)

  Eval vm_compute in List.nth 252 (fst c1) _.
  (* 253. *)
  Definition s253_1 := Eval vm_compute in (step_checker s252_1 (List.nth 252 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s253_1.
  (* s253_1 = ({|  |} *)

  Eval vm_compute in List.nth 253 (fst c1) _.
  (* 254. *)
  Definition s254_1 := Eval vm_compute in (step_checker s253_1 (List.nth 253 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s254_1.
  (* s254_1 = ({|  |} *)

  Eval vm_compute in List.nth 254 (fst c1) _.
  (* 255. *)
  Definition s255_1 := Eval vm_compute in (step_checker s254_1 (List.nth 254 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s255_1.
  (* s255_1 = ({|  |} *)

  Eval vm_compute in List.nth 255 (fst c1) _.
  (* 256. *)
  Definition s256_1 := Eval vm_compute in (step_checker s255_1 (List.nth 255 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s256_1.
  (* s256_1 = ({|  |} *)

  Eval vm_compute in List.nth 256 (fst c1) _.
  (* 257. *)
  Definition s257_1 := Eval vm_compute in (step_checker s256_1 (List.nth 256 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s257_1.
  (* s257_1 = ({|  |} *)

  Eval vm_compute in List.nth 257 (fst c1) _.
  (* 258. *)
  Definition s258_1 := Eval vm_compute in (step_checker s257_1 (List.nth 257 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s258_1.
  (* s258_1 = ({|  |} *)

  Eval vm_compute in List.nth 258 (fst c1) _.
  (* 259. *)
  Definition s259_1 := Eval vm_compute in (step_checker s258_1 (List.nth 258 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s259_1.
  (* s259_1 = ({|  |} *)

  Eval vm_compute in List.nth 259 (fst c1) _.
  (* 260. *)
  Definition s260_1 := Eval vm_compute in (step_checker s259_1 (List.nth 259 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s260_1.
  (* s260_1 = ({|  |} *)

  Eval vm_compute in List.nth 260 (fst c1) _.
  (* 261. *)
  Definition s261_1 := Eval vm_compute in (step_checker s260_1 (List.nth 260 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s261_1.
  (* s261_1 = ({|  |} *)

  Eval vm_compute in List.nth 261 (fst c1) _.
  (* 262. *)
  Definition s262_1 := Eval vm_compute in (step_checker s261_1 (List.nth 261 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s262_1.
  (* s262_1 = ({|  |} *)

  Eval vm_compute in List.nth 262 (fst c1) _.
  (* 263. *)
  Definition s263_1 := Eval vm_compute in (step_checker s262_1 (List.nth 262 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s263_1.
  (* s263_1 = ({|  |} *)

  Eval vm_compute in List.nth 263 (fst c1) _.
  (* 264. *)
  Definition s264_1 := Eval vm_compute in (step_checker s263_1 (List.nth 263 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s264_1.
  (* s264_1 = ({|  |} *)

  Eval vm_compute in List.nth 264 (fst c1) _.
  (* 265. *)
  Definition s265_1 := Eval vm_compute in (step_checker s264_1 (List.nth 264 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s265_1.
  (* s265_1 = ({|  |} *)

  Eval vm_compute in List.nth 265 (fst c1) _.
  (* 266. *)
  Definition s266_1 := Eval vm_compute in (step_checker s265_1 (List.nth 265 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s266_1.
  (* s266_1 = ({|  |} *)

  Eval vm_compute in List.nth 266 (fst c1) _.
  (* 267. *)
  Definition s267_1 := Eval vm_compute in (step_checker s266_1 (List.nth 266 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s267_1.
  (* s267_1 = ({|  |} *)

  Eval vm_compute in List.nth 267 (fst c1) _.
  (* 268. *)
  Definition s268_1 := Eval vm_compute in (step_checker s267_1 (List.nth 267 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s268_1.
  (* s268_1 = ({|  |} *)

  Eval vm_compute in List.nth 268 (fst c1) _.
  (* 269. *)
  Definition s269_1 := Eval vm_compute in (step_checker s268_1 (List.nth 268 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s269_1.
  (* s269_1 = ({|  |} *)

  Eval vm_compute in List.nth 269 (fst c1) _.
  (* 270. *)
  Definition s270_1 := Eval vm_compute in (step_checker s269_1 (List.nth 269 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s270_1.
  (* s270_1 = ({|  |} *)

  Eval vm_compute in List.nth 270 (fst c1) _.
  (* 271. *)
  Definition s271_1 := Eval vm_compute in (step_checker s270_1 (List.nth 270 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s271_1.
  (* s271_1 = ({|  |} *)

  Eval vm_compute in List.nth 271 (fst c1) _.
  (* 272. *)
  Definition s272_1 := Eval vm_compute in (step_checker s271_1 (List.nth 271 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s272_1.
  (* s272_1 = ({|  |} *)

  Eval vm_compute in List.nth 272 (fst c1) _.
  (* 273. *)
  Definition s273_1 := Eval vm_compute in (step_checker s272_1 (List.nth 272 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s273_1.
  (* s273_1 = ({|  |} *)

  Eval vm_compute in List.nth 273 (fst c1) _.
  (* 274. *)
  Definition s274_1 := Eval vm_compute in (step_checker s273_1 (List.nth 273 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s274_1.
  (* s274_1 = ({|  |} *)

  Eval vm_compute in List.nth 274 (fst c1) _.
  (* 275. *)
  Definition s275_1 := Eval vm_compute in (step_checker s274_1 (List.nth 274 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s275_1.
  (* s275_1 = ({|  |} *)

  Eval vm_compute in List.nth 275 (fst c1) _.
  (* 276. *)
  Definition s276_1 := Eval vm_compute in (step_checker s275_1 (List.nth 275 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s276_1.
  (* s276_1 = ({|  |} *)

  Eval vm_compute in List.nth 276 (fst c1) _.
  (* 277. *)
  Definition s277_1 := Eval vm_compute in (step_checker s276_1 (List.nth 276 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s277_1.
  (* s277_1 = ({|  |} *)

  Eval vm_compute in List.nth 277 (fst c1) _.
  (* 278. *)
  Definition s278_1 := Eval vm_compute in (step_checker s277_1 (List.nth 277 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s278_1.
  (* s278_1 = ({|  |} *)

  Eval vm_compute in List.nth 278 (fst c1) _.
  (* 279. *)
  Definition s279_1 := Eval vm_compute in (step_checker s278_1 (List.nth 278 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s279_1.
  (* s279_1 = ({|  |} *)

  Eval vm_compute in List.nth 279 (fst c1) _.
  (* 280. *)
  Definition s280_1 := Eval vm_compute in (step_checker s279_1 (List.nth 279 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s280_1.
  (* s280_1 = ({|  |} *)

  Eval vm_compute in List.nth 280 (fst c1) _.
  (* 281. *)
  Definition s281_1 := Eval vm_compute in (step_checker s280_1 (List.nth 280 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s281_1.
  (* s281_1 = ({|  |} *)

  Eval vm_compute in List.nth 281 (fst c1) _.
  (* 282. *)
  Definition s282_1 := Eval vm_compute in (step_checker s281_1 (List.nth 281 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s282_1.
  (* s282_1 = ({|  |} *)

  Eval vm_compute in List.nth 282 (fst c1) _.
  (* 283. *)
  Definition s283_1 := Eval vm_compute in (step_checker s282_1 (List.nth 282 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s283_1.
  (* s283_1 = ({|  |} *)

  Eval vm_compute in List.nth 283 (fst c1) _.
  (* 284. *)
  Definition s284_1 := Eval vm_compute in (step_checker s283_1 (List.nth 283 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s284_1.
  (* s284_1 = ({|  |} *)

  Eval vm_compute in List.nth 284 (fst c1) _.
  (* 285. *)
  Definition s285_1 := Eval vm_compute in (step_checker s284_1 (List.nth 284 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s285_1.
  (* s285_1 = ({|  |} *)

  Eval vm_compute in List.nth 285 (fst c1) _.
  (* 286. *)
  Definition s286_1 := Eval vm_compute in (step_checker s285_1 (List.nth 285 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s286_1.
  (* s286_1 = ({|  |} *)

  Eval vm_compute in List.nth 286 (fst c1) _.
  (* 287. *)
  Definition s287_1 := Eval vm_compute in (step_checker s286_1 (List.nth 286 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s287_1.
  (* s287_1 = ({|  |} *)

  Eval vm_compute in List.nth 287 (fst c1) _.
  (* 288. *)
  Definition s288_1 := Eval vm_compute in (step_checker s287_1 (List.nth 287 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s288_1.
  (* s288_1 = ({|  |} *)

  Eval vm_compute in List.nth 288 (fst c1) _.
  (* 289. *)
  Definition s289_1 := Eval vm_compute in (step_checker s288_1 (List.nth 288 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s289_1.
  (* s289_1 = ({|  |} *)

  Eval vm_compute in List.nth 289 (fst c1) _.
  (* 290. *)
  Definition s290_1 := Eval vm_compute in (step_checker s289_1 (List.nth 289 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s290_1.
  (* s290_1 = ({|  |} *)

  Eval vm_compute in List.nth 290 (fst c1) _.
  (* 291. *)
  Definition s291_1 := Eval vm_compute in (step_checker s290_1 (List.nth 290 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s291_1.
  (* s291_1 = ({|  |} *)

  Eval vm_compute in List.nth 291 (fst c1) _.
  (* 292. *)
  Definition s292_1 := Eval vm_compute in (step_checker s291_1 (List.nth 291 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s292_1.
  (* s292_1 = ({|  |} *)

  Eval vm_compute in List.nth 292 (fst c1) _.
  (* 293. *)
  Definition s293_1 := Eval vm_compute in (step_checker s292_1 (List.nth 292 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s293_1.
  (* s293_1 = ({|  |} *)

  Eval vm_compute in List.nth 293 (fst c1) _.
  (* 294. *)
  Definition s294_1 := Eval vm_compute in (step_checker s293_1 (List.nth 293 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s294_1.
  (* s294_1 = ({|  |} *)

  Eval vm_compute in List.nth 294 (fst c1) _.
  (* 295. *)
  Definition s295_1 := Eval vm_compute in (step_checker s294_1 (List.nth 294 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s295_1.
  (* s295_1 = ({|  |} *)

  Eval vm_compute in List.nth 295 (fst c1) _.
  (* 296. *)
  Definition s296_1 := Eval vm_compute in (step_checker s295_1 (List.nth 295 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s296_1.
  (* s296_1 = ({|  |} *)

  Eval vm_compute in List.nth 296 (fst c1) _.
  (* 297. *)
  Definition s297_1 := Eval vm_compute in (step_checker s296_1 (List.nth 296 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s297_1.
  (* s297_1 = ({|  |} *)

  Eval vm_compute in List.nth 297 (fst c1) _.
  (* 298. *)
  Definition s298_1 := Eval vm_compute in (step_checker s297_1 (List.nth 297 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s298_1.
  (* s298_1 = ({|  |} *)

  Eval vm_compute in List.nth 298 (fst c1) _.
  (* 299. *)
  Definition s299_1 := Eval vm_compute in (step_checker s298_1 (List.nth 298 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s299_1.
  (* s299_1 = ({|  |} *)

  Eval vm_compute in List.nth 299 (fst c1) _.
  (* 300. *)
  Definition s300_1 := Eval vm_compute in (step_checker s299_1 (List.nth 299 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s300_1.
  (* s300_1 = ({|  |} *)

  Eval vm_compute in List.nth 300 (fst c1) _.
  (* 301. *)
  Definition s301_1 := Eval vm_compute in (step_checker s300_1 (List.nth 300 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s301_1.
  (* s301_1 = ({|  |} *)

  Eval vm_compute in List.nth 301 (fst c1) _.
  (* 302. *)
  Definition s302_1 := Eval vm_compute in (step_checker s301_1 (List.nth 301 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s302_1.
  (* s302_1 = ({|  |} *)

  Eval vm_compute in List.nth 302 (fst c1) _.
  (* 303. *)
  Definition s303_1 := Eval vm_compute in (step_checker s302_1 (List.nth 302 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s303_1.
  (* s303_1 = ({|  |} *)

  Eval vm_compute in List.nth 303 (fst c1) _.
  (* 304. *)
  Definition s304_1 := Eval vm_compute in (step_checker s303_1 (List.nth 303 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s304_1.
  (* s304_1 = ({|  |} *)

  Eval vm_compute in List.nth 304 (fst c1) _.
  (* 305. *)
  Definition s305_1 := Eval vm_compute in (step_checker s304_1 (List.nth 304 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s305_1.
  (* s305_1 = ({|  |} *)

  Eval vm_compute in List.nth 305 (fst c1) _.
  (* 306. *)
  Definition s306_1 := Eval vm_compute in (step_checker s305_1 (List.nth 305 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s306_1.
  (* s306_1 = ({|  |} *)

  Eval vm_compute in List.nth 306 (fst c1) _.
  (* 307. *)
  Definition s307_1 := Eval vm_compute in (step_checker s306_1 (List.nth 306 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s307_1.
  (* s307_1 = ({|  |} *)

  Eval vm_compute in List.nth 307 (fst c1) _.
  (* 308. *)
  Definition s308_1 := Eval vm_compute in (step_checker s307_1 (List.nth 307 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s308_1.
  (* s308_1 = ({|  |} *)

  Eval vm_compute in List.nth 308 (fst c1) _.
  (* 309. *)
  Definition s309_1 := Eval vm_compute in (step_checker s308_1 (List.nth 308 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s309_1.
  (* s309_1 = ({|  |} *)

  Eval vm_compute in List.nth 309 (fst c1) _.
  (* 310. *)
  Definition s310_1 := Eval vm_compute in (step_checker s309_1 (List.nth 309 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s310_1.
  (* s310_1 = ({|  |} *)

  Eval vm_compute in List.nth 310 (fst c1) _.
  (* 311. *)
  Definition s311_1 := Eval vm_compute in (step_checker s310_1 (List.nth 310 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s311_1.
  (* s311_1 = ({|  |} *)

  Eval vm_compute in List.nth 311 (fst c1) _.
  (* 312. *)
  Definition s312_1 := Eval vm_compute in (step_checker s311_1 (List.nth 311 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s312_1.
  (* s312_1 = ({|  |} *)

  Eval vm_compute in List.nth 312 (fst c1) _.
  (* 313. *)
  Definition s313_1 := Eval vm_compute in (step_checker s312_1 (List.nth 312 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s313_1.
  (* s313_1 = ({|  |} *)

  Eval vm_compute in List.nth 313 (fst c1) _.
  (* 314. *)
  Definition s314_1 := Eval vm_compute in (step_checker s313_1 (List.nth 313 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s314_1.
  (* s314_1 = ({|  |} *)

  Eval vm_compute in List.nth 314 (fst c1) _.
  (* 315. *)
  Definition s315_1 := Eval vm_compute in (step_checker s314_1 (List.nth 314 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s315_1.
  (* s315_1 = ({|  |} *)

  Eval vm_compute in List.nth 315 (fst c1) _.
  (* 316. *)
  Definition s316_1 := Eval vm_compute in (step_checker s315_1 (List.nth 315 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s316_1.
  (* s316_1 = ({|  |} *)

  Eval vm_compute in List.nth 316 (fst c1) _.
  (* 317. *)
  Definition s317_1 := Eval vm_compute in (step_checker s316_1 (List.nth 316 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s317_1.
  (* s317_1 = ({|  |} *)

  Eval vm_compute in List.nth 317 (fst c1) _.
  (* 318. *)
  Definition s318_1 := Eval vm_compute in (step_checker s317_1 (List.nth 317 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s318_1.
  (* s318_1 = ({|  |} *)

  Eval vm_compute in List.nth 318 (fst c1) _.
  (* 319. *)
  Definition s319_1 := Eval vm_compute in (step_checker s318_1 (List.nth 318 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s319_1.
  (* s319_1 = ({|  |} *)

  Eval vm_compute in List.nth 319 (fst c1) _.
  (* 320. *)
  Definition s320_1 := Eval vm_compute in (step_checker s319_1 (List.nth 319 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s320_1.
  (* s320_1 = ({|  |} *)

  Eval vm_compute in List.nth 320 (fst c1) _.
  (* 321. *)
  Definition s321_1 := Eval vm_compute in (step_checker s320_1 (List.nth 320 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s321_1.
  (* s321_1 = ({|  |} *)

  Eval vm_compute in List.nth 321 (fst c1) _.
  (* 322. *)
  Definition s322_1 := Eval vm_compute in (step_checker s321_1 (List.nth 321 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s322_1.
  (* s322_1 = ({|  |} *)

  Eval vm_compute in List.nth 322 (fst c1) _.
  (* 323. *)
  Definition s323_1 := Eval vm_compute in (step_checker s322_1 (List.nth 322 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s323_1.
  (* s323_1 = ({|  |} *)

  Eval vm_compute in List.nth 323 (fst c1) _.
  (* 324. *)
  Definition s324_1 := Eval vm_compute in (step_checker s323_1 (List.nth 323 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s324_1.
  (* s324_1 = ({|  |} *)

  Eval vm_compute in List.nth 324 (fst c1) _.
  (* 325. *)
  Definition s325_1 := Eval vm_compute in (step_checker s324_1 (List.nth 324 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s325_1.
  (* s325_1 = ({|  |} *)

  Eval vm_compute in List.nth 325 (fst c1) _.
  (* 326. *)
  Definition s326_1 := Eval vm_compute in (step_checker s325_1 (List.nth 325 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s326_1.
  (* s326_1 = ({|  |} *)

  Eval vm_compute in List.nth 326 (fst c1) _.
  (* 327. *)
  Definition s327_1 := Eval vm_compute in (step_checker s326_1 (List.nth 326 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s327_1.
  (* s327_1 = ({|  |} *)

  Eval vm_compute in List.nth 327 (fst c1) _.
  (* 328. *)
  Definition s328_1 := Eval vm_compute in (step_checker s327_1 (List.nth 327 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s328_1.
  (* s328_1 = ({|  |} *)

  Eval vm_compute in List.nth 328 (fst c1) _.
  (* 329. *)
  Definition s329_1 := Eval vm_compute in (step_checker s328_1 (List.nth 328 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s329_1.
  (* s329_1 = ({|  |} *)

  Eval vm_compute in List.nth 329 (fst c1) _.
  (* 330. *)
  Definition s330_1 := Eval vm_compute in (step_checker s329_1 (List.nth 329 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s330_1.
  (* s330_1 = ({|  |} *)

  Eval vm_compute in List.nth 330 (fst c1) _.
  (* 331. *)
  Definition s331_1 := Eval vm_compute in (step_checker s330_1 (List.nth 330 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s331_1.
  (* s331_1 = ({|  |} *)

  Eval vm_compute in List.nth 331 (fst c1) _.
  (* 332. *)
  Definition s332_1 := Eval vm_compute in (step_checker s331_1 (List.nth 331 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s332_1.
  (* s332_1 = ({|  |} *)

  Eval vm_compute in List.nth 332 (fst c1) _.
  (* 333. *)
  Definition s333_1 := Eval vm_compute in (step_checker s332_1 (List.nth 332 (fst c1) (CTrue t_func1 t_atom1 t_form1 0))).
  Print s333_1.
  (* s333_1 = ({|  |} *)

End Test1Debug.
