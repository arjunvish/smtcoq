Add Rec LoadPath "../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool. 
Require Import Int31. 
Local Open Scope int31_scope.

Section thesistest1debug. 

 Parse_certif_verit t_i t_func t_atom t_form root used_roots trace 
 "thesistest1/thesistest1.smt2" 
 "thesistest1/thesistest1.pf". 

 Definition nclauses := Eval vm_compute in (match trace with Certif a _ _ => a end). (* Size of the state *)
 Print nclauses.

  Definition c := Eval vm_compute in (match trace with Certif _ a _ => a end). (* Certificate *)
 Definition conf := Eval vm_compute in (match trace with Certif _ _ a => a end). (* Look here in the state for the empty clause*)
 Print conf.

 Eval vm_compute in List.length (fst c). (* No. of steps in certificate *) 

 Eval vm_compute in (Form.check_form t_form && Atom.check_atom t_atom && Atom.wt t_i t_func t_atom).

 Definition s0 := Eval vm_compute in (add_roots (S.make nclauses) root used_roots).
 Print s0.

 Eval vm_compute in List.nth 0 (fst c) _.

 Definition s1 := Eval vm_compute in (step_checker s0 (List.nth 0 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s1. 


 Eval vm_compute in List.nth 1 (fst c) _.

 Definition s2 := Eval vm_compute in (step_checker s1 (List.nth 1 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s2. 


 Eval vm_compute in List.nth 2 (fst c) _.

 Definition s3 := Eval vm_compute in (step_checker s2 (List.nth 2 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s3. 


 Eval vm_compute in List.nth 3 (fst c) _.

 Definition s4 := Eval vm_compute in (step_checker s3 (List.nth 3 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s4. 


 Eval vm_compute in List.nth 4 (fst c) _.

 Definition s5 := Eval vm_compute in (step_checker s4 (List.nth 4 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s5. 


 Eval vm_compute in List.nth 5 (fst c) _.

 Definition s6 := Eval vm_compute in (step_checker s5 (List.nth 5 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s6. 


 Eval vm_compute in List.nth 6 (fst c) _.

 Definition s7 := Eval vm_compute in (step_checker s6 (List.nth 6 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s7. 


 Eval vm_compute in List.nth 7 (fst c) _.

 Definition s8 := Eval vm_compute in (step_checker s7 (List.nth 7 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s8. 


 Eval vm_compute in List.nth 8 (fst c) _.

 Definition s9 := Eval vm_compute in (step_checker s8 (List.nth 8 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s9. 


 Eval vm_compute in List.nth 9 (fst c) _.

 Definition s10 := Eval vm_compute in (step_checker s9 (List.nth 9 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s10. 


 Eval vm_compute in List.nth 10 (fst c) _.

 Definition s11 := Eval vm_compute in (step_checker s10 (List.nth 10 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s11. 


 Eval vm_compute in List.nth 11 (fst c) _.

 Definition s12 := Eval vm_compute in (step_checker s11 (List.nth 11 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s12. 


 Eval vm_compute in List.nth 12 (fst c) _.

 Definition s13 := Eval vm_compute in (step_checker s12 (List.nth 12 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s13. 


 Eval vm_compute in List.nth 13 (fst c) _.

 Definition s14 := Eval vm_compute in (step_checker s13 (List.nth 13 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s14. 


 Eval vm_compute in List.nth 14 (fst c) _.

 Definition s15 := Eval vm_compute in (step_checker s14 (List.nth 14 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s15. 


 Eval vm_compute in List.nth 15 (fst c) _.

 Definition s16 := Eval vm_compute in (step_checker s15 (List.nth 15 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s16. 


 Eval vm_compute in List.nth 16 (fst c) _.

 Definition s17 := Eval vm_compute in (step_checker s16 (List.nth 16 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s17. 


 Eval vm_compute in List.nth 17 (fst c) _.

 Definition s18 := Eval vm_compute in (step_checker s17 (List.nth 17 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s18. 


 Eval vm_compute in List.nth 18 (fst c) _.

 Definition s19 := Eval vm_compute in (step_checker s18 (List.nth 18 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s19. 


 Eval vm_compute in List.nth 19 (fst c) _.

 Definition s20 := Eval vm_compute in (step_checker s19 (List.nth 19 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s20. 


 Eval vm_compute in List.nth 20 (fst c) _.

 Definition s21 := Eval vm_compute in (step_checker s20 (List.nth 20 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s21. 


 Eval vm_compute in List.nth 21 (fst c) _.

 Definition s22 := Eval vm_compute in (step_checker s21 (List.nth 21 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s22. 


 Eval vm_compute in List.nth 22 (fst c) _.

 Definition s23 := Eval vm_compute in (step_checker s22 (List.nth 22 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s23. 


 Eval vm_compute in List.nth 23 (fst c) _.

 Definition s24 := Eval vm_compute in (step_checker s23 (List.nth 23 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s24. 


 Eval vm_compute in List.nth 24 (fst c) _.

 Definition s25 := Eval vm_compute in (step_checker s24 (List.nth 24 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s25. 


 Eval vm_compute in List.nth 25 (fst c) _.

 Definition s26 := Eval vm_compute in (step_checker s25 (List.nth 25 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s26. 


 Eval vm_compute in List.nth 26 (fst c) _.

 Definition s27 := Eval vm_compute in (step_checker s26 (List.nth 26 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s27. 


 Eval vm_compute in List.nth 27 (fst c) _.

 Definition s28 := Eval vm_compute in (step_checker s27 (List.nth 27 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s28. 


 Eval vm_compute in List.nth 28 (fst c) _.

 Definition s29 := Eval vm_compute in (step_checker s28 (List.nth 28 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s29. 


 Eval vm_compute in List.nth 29 (fst c) _.

 Definition s30 := Eval vm_compute in (step_checker s29 (List.nth 29 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s30. 


 Eval vm_compute in List.nth 30 (fst c) _.

 Definition s31 := Eval vm_compute in (step_checker s30 (List.nth 30 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s31. 


 Eval vm_compute in List.nth 31 (fst c) _.

 Definition s32 := Eval vm_compute in (step_checker s31 (List.nth 31 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s32. 


 Eval vm_compute in List.nth 32 (fst c) _.

 Definition s33 := Eval vm_compute in (step_checker s32 (List.nth 32 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s33. 


 Eval vm_compute in List.nth 33 (fst c) _.

 Definition s34 := Eval vm_compute in (step_checker s33 (List.nth 33 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s34. 


 Eval vm_compute in List.nth 34 (fst c) _.

 Definition s35 := Eval vm_compute in (step_checker s34 (List.nth 34 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s35. 


 Eval vm_compute in List.nth 35 (fst c) _.

 Definition s36 := Eval vm_compute in (step_checker s35 (List.nth 35 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s36. 


 Eval vm_compute in List.nth 36 (fst c) _.

 Definition s37 := Eval vm_compute in (step_checker s36 (List.nth 36 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s37. 


 Eval vm_compute in List.nth 37 (fst c) _.

 Definition s38 := Eval vm_compute in (step_checker s37 (List.nth 37 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s38. 


 Eval vm_compute in List.nth 38 (fst c) _.

 Definition s39 := Eval vm_compute in (step_checker s38 (List.nth 38 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s39. 


 Eval vm_compute in List.nth 39 (fst c) _.

 Definition s40 := Eval vm_compute in (step_checker s39 (List.nth 39 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s40. 


 Eval vm_compute in List.nth 40 (fst c) _.

 Definition s41 := Eval vm_compute in (step_checker s40 (List.nth 40 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s41. 


 Eval vm_compute in List.nth 41 (fst c) _.

 Definition s42 := Eval vm_compute in (step_checker s41 (List.nth 41 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s42. 


 Eval vm_compute in List.nth 42 (fst c) _.

 Definition s43 := Eval vm_compute in (step_checker s42 (List.nth 42 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s43. 


 Eval vm_compute in List.nth 43 (fst c) _.

 Definition s44 := Eval vm_compute in (step_checker s43 (List.nth 43 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s44. 


 Eval vm_compute in List.nth 44 (fst c) _.

 Definition s45 := Eval vm_compute in (step_checker s44 (List.nth 44 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s45. 


 Eval vm_compute in List.nth 45 (fst c) _.

 Definition s46 := Eval vm_compute in (step_checker s45 (List.nth 45 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s46. 


 Eval vm_compute in List.nth 46 (fst c) _.

 Definition s47 := Eval vm_compute in (step_checker s46 (List.nth 46 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s47. 


 Eval vm_compute in List.nth 47 (fst c) _.

 Definition s48 := Eval vm_compute in (step_checker s47 (List.nth 47 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s48. 


 Eval vm_compute in List.nth 48 (fst c) _.

 Definition s49 := Eval vm_compute in (step_checker s48 (List.nth 48 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s49. 


 Eval vm_compute in List.nth 49 (fst c) _.

 Definition s50 := Eval vm_compute in (step_checker s49 (List.nth 49 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s50. 


 Eval vm_compute in List.nth 50 (fst c) _.

 Definition s51 := Eval vm_compute in (step_checker s50 (List.nth 50 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s51. 


 Eval vm_compute in List.nth 51 (fst c) _.

 Definition s52 := Eval vm_compute in (step_checker s51 (List.nth 51 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s52. 


 Eval vm_compute in List.nth 52 (fst c) _.

 Definition s53 := Eval vm_compute in (step_checker s52 (List.nth 52 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s53. 


 Eval vm_compute in List.nth 53 (fst c) _.

 Definition s54 := Eval vm_compute in (step_checker s53 (List.nth 53 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s54. 


 Eval vm_compute in List.nth 54 (fst c) _.

 Definition s55 := Eval vm_compute in (step_checker s54 (List.nth 54 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s55. 


 Eval vm_compute in List.nth 55 (fst c) _.

 Definition s56 := Eval vm_compute in (step_checker s55 (List.nth 55 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s56. 


 Eval vm_compute in List.nth 56 (fst c) _.

 Definition s57 := Eval vm_compute in (step_checker s56 (List.nth 56 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s57. 


 Eval vm_compute in List.nth 57 (fst c) _.

 Definition s58 := Eval vm_compute in (step_checker s57 (List.nth 57 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s58. 


 Eval vm_compute in List.nth 58 (fst c) _.

 Definition s59 := Eval vm_compute in (step_checker s58 (List.nth 58 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s59. 


 Eval vm_compute in List.nth 59 (fst c) _.

 Definition s60 := Eval vm_compute in (step_checker s59 (List.nth 59 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s60. 


 Eval vm_compute in List.nth 60 (fst c) _.

 Definition s61 := Eval vm_compute in (step_checker s60 (List.nth 60 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s61. 


 Eval vm_compute in List.nth 61 (fst c) _.

 Definition s62 := Eval vm_compute in (step_checker s61 (List.nth 61 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s62. 


 Eval vm_compute in List.nth 62 (fst c) _.

 Definition s63 := Eval vm_compute in (step_checker s62 (List.nth 62 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s63. 


 Eval vm_compute in List.nth 63 (fst c) _.

 Definition s64 := Eval vm_compute in (step_checker s63 (List.nth 63 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s64. 


 Eval vm_compute in List.nth 64 (fst c) _.

 Definition s65 := Eval vm_compute in (step_checker s64 (List.nth 64 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s65. 


 Eval vm_compute in List.nth 65 (fst c) _.

 Definition s66 := Eval vm_compute in (step_checker s65 (List.nth 65 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s66. 


 Eval vm_compute in List.nth 66 (fst c) _.

 Definition s67 := Eval vm_compute in (step_checker s66 (List.nth 66 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s67. 


 Eval vm_compute in List.nth 67 (fst c) _.

 Definition s68 := Eval vm_compute in (step_checker s67 (List.nth 67 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s68. 


 Eval vm_compute in List.nth 68 (fst c) _.

 Definition s69 := Eval vm_compute in (step_checker s68 (List.nth 68 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s69. 


 Eval vm_compute in List.nth 69 (fst c) _.

 Definition s70 := Eval vm_compute in (step_checker s69 (List.nth 69 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s70. 


 Eval vm_compute in List.nth 70 (fst c) _.

 Definition s71 := Eval vm_compute in (step_checker s70 (List.nth 70 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s71. 


 Eval vm_compute in List.nth 71 (fst c) _.

 Definition s72 := Eval vm_compute in (step_checker s71 (List.nth 71 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s72. 


 Eval vm_compute in List.nth 72 (fst c) _.

 Definition s73 := Eval vm_compute in (step_checker s72 (List.nth 72 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s73. 


 Eval vm_compute in List.nth 73 (fst c) _.

 Definition s74 := Eval vm_compute in (step_checker s73 (List.nth 73 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s74. 


 Eval vm_compute in List.nth 74 (fst c) _.

 Definition s75 := Eval vm_compute in (step_checker s74 (List.nth 74 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s75. 


 Eval vm_compute in List.nth 75 (fst c) _.

 Definition s76 := Eval vm_compute in (step_checker s75 (List.nth 75 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s76. 


 Eval vm_compute in List.nth 76 (fst c) _.

 Definition s77 := Eval vm_compute in (step_checker s76 (List.nth 76 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s77. 


 Eval vm_compute in List.nth 77 (fst c) _.

 Definition s78 := Eval vm_compute in (step_checker s77 (List.nth 77 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s78. 


 Eval vm_compute in List.nth 78 (fst c) _.

 Definition s79 := Eval vm_compute in (step_checker s78 (List.nth 78 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s79. 


 Eval vm_compute in List.nth 79 (fst c) _.

 Definition s80 := Eval vm_compute in (step_checker s79 (List.nth 79 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s80. 


 Eval vm_compute in List.nth 80 (fst c) _.

 Definition s81 := Eval vm_compute in (step_checker s80 (List.nth 80 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s81. 


 Eval vm_compute in List.nth 81 (fst c) _.

 Definition s82 := Eval vm_compute in (step_checker s81 (List.nth 81 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s82. 


 Eval vm_compute in List.nth 82 (fst c) _.

 Definition s83 := Eval vm_compute in (step_checker s82 (List.nth 82 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s83. 


 Eval vm_compute in List.nth 83 (fst c) _.

 Definition s84 := Eval vm_compute in (step_checker s83 (List.nth 83 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s84. 


 Eval vm_compute in List.nth 84 (fst c) _.

 Definition s85 := Eval vm_compute in (step_checker s84 (List.nth 84 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s85. 


 Eval vm_compute in List.nth 85 (fst c) _.

 Definition s86 := Eval vm_compute in (step_checker s85 (List.nth 85 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s86. 


 Eval vm_compute in List.nth 86 (fst c) _.

 Definition s87 := Eval vm_compute in (step_checker s86 (List.nth 86 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s87. 


 Eval vm_compute in List.nth 87 (fst c) _.

 Definition s88 := Eval vm_compute in (step_checker s87 (List.nth 87 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s88. 


 Eval vm_compute in List.nth 88 (fst c) _.

 Definition s89 := Eval vm_compute in (step_checker s88 (List.nth 88 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s89. 


 Eval vm_compute in List.nth 89 (fst c) _.

 Definition s90 := Eval vm_compute in (step_checker s89 (List.nth 89 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s90. 


 Eval vm_compute in List.nth 90 (fst c) _.

 Definition s91 := Eval vm_compute in (step_checker s90 (List.nth 90 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s91. 


 Eval vm_compute in List.nth 91 (fst c) _.

 Definition s92 := Eval vm_compute in (step_checker s91 (List.nth 91 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s92. 


 Eval vm_compute in List.nth 92 (fst c) _.

 Definition s93 := Eval vm_compute in (step_checker s92 (List.nth 92 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s93. 


 Eval vm_compute in List.nth 93 (fst c) _.

 Definition s94 := Eval vm_compute in (step_checker s93 (List.nth 93 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s94. 


 Eval vm_compute in List.nth 94 (fst c) _.

 Definition s95 := Eval vm_compute in (step_checker s94 (List.nth 94 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s95. 


 Eval vm_compute in List.nth 95 (fst c) _.

 Definition s96 := Eval vm_compute in (step_checker s95 (List.nth 95 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s96. 


 Eval vm_compute in List.nth 96 (fst c) _.

 Definition s97 := Eval vm_compute in (step_checker s96 (List.nth 96 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s97. 


 Eval vm_compute in List.nth 97 (fst c) _.

 Definition s98 := Eval vm_compute in (step_checker s97 (List.nth 97 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s98. 

End thesistest1debug.