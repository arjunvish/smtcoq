Add Rec LoadPath "../../src" as SMTCoq.
Require Import SMTCoq.SMTCoq.
Require Import Bool. 
Require Import Int31. 
Local Open Scope int31_scope.

Section test7veritrun.

 Parse_certif_verit t_i t_func t_atom t_form root used_roots trace 
 "test7verit/test7verit.smt2" 
 "test7verit/test7verit.pf". 

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


 Eval vm_compute in List.nth 98 (fst c) _.

 Definition s99 := Eval vm_compute in (step_checker s98 (List.nth 98 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s99. 


 Eval vm_compute in List.nth 99 (fst c) _.

 Definition s100 := Eval vm_compute in (step_checker s99 (List.nth 99 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s100. 


 Eval vm_compute in List.nth 100 (fst c) _.

 Definition s101 := Eval vm_compute in (step_checker s100 (List.nth 100 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s101. 


 Eval vm_compute in List.nth 101 (fst c) _.

 Definition s102 := Eval vm_compute in (step_checker s101 (List.nth 101 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s102. 


 Eval vm_compute in List.nth 102 (fst c) _.

 Definition s103 := Eval vm_compute in (step_checker s102 (List.nth 102 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s103. 


 Eval vm_compute in List.nth 103 (fst c) _.

 Definition s104 := Eval vm_compute in (step_checker s103 (List.nth 103 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s104. 


 Eval vm_compute in List.nth 104 (fst c) _.

 Definition s105 := Eval vm_compute in (step_checker s104 (List.nth 104 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s105. 


 Eval vm_compute in List.nth 105 (fst c) _.

 Definition s106 := Eval vm_compute in (step_checker s105 (List.nth 105 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s106. 


 Eval vm_compute in List.nth 106 (fst c) _.

 Definition s107 := Eval vm_compute in (step_checker s106 (List.nth 106 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s107. 


 Eval vm_compute in List.nth 107 (fst c) _.

 Definition s108 := Eval vm_compute in (step_checker s107 (List.nth 107 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s108. 


 Eval vm_compute in List.nth 108 (fst c) _.

 Definition s109 := Eval vm_compute in (step_checker s108 (List.nth 108 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s109. 


 Eval vm_compute in List.nth 109 (fst c) _.

 Definition s110 := Eval vm_compute in (step_checker s109 (List.nth 109 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s110. 


 Eval vm_compute in List.nth 110 (fst c) _.

 Definition s111 := Eval vm_compute in (step_checker s110 (List.nth 110 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s111. 


 Eval vm_compute in List.nth 111 (fst c) _.

 Definition s112 := Eval vm_compute in (step_checker s111 (List.nth 111 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s112. 


 Eval vm_compute in List.nth 112 (fst c) _.

 Definition s113 := Eval vm_compute in (step_checker s112 (List.nth 112 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s113. 


 Eval vm_compute in List.nth 113 (fst c) _.

 Definition s114 := Eval vm_compute in (step_checker s113 (List.nth 113 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s114. 


 Eval vm_compute in List.nth 114 (fst c) _.

 Definition s115 := Eval vm_compute in (step_checker s114 (List.nth 114 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s115. 


 Eval vm_compute in List.nth 115 (fst c) _.

 Definition s116 := Eval vm_compute in (step_checker s115 (List.nth 115 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s116. 


 Eval vm_compute in List.nth 116 (fst c) _.

 Definition s117 := Eval vm_compute in (step_checker s116 (List.nth 116 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s117. 


 Eval vm_compute in List.nth 117 (fst c) _.

 Definition s118 := Eval vm_compute in (step_checker s117 (List.nth 117 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s118. 


 Eval vm_compute in List.nth 118 (fst c) _.

 Definition s119 := Eval vm_compute in (step_checker s118 (List.nth 118 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s119. 


 Eval vm_compute in List.nth 119 (fst c) _.

 Definition s120 := Eval vm_compute in (step_checker s119 (List.nth 119 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s120. 


 Eval vm_compute in List.nth 120 (fst c) _.

 Definition s121 := Eval vm_compute in (step_checker s120 (List.nth 120 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s121. 


 Eval vm_compute in List.nth 121 (fst c) _.

 Definition s122 := Eval vm_compute in (step_checker s121 (List.nth 121 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s122. 


 Eval vm_compute in List.nth 122 (fst c) _.

 Definition s123 := Eval vm_compute in (step_checker s122 (List.nth 122 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s123. 


 Eval vm_compute in List.nth 123 (fst c) _.

 Definition s124 := Eval vm_compute in (step_checker s123 (List.nth 123 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s124. 


 Eval vm_compute in List.nth 124 (fst c) _.

 Definition s125 := Eval vm_compute in (step_checker s124 (List.nth 124 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s125. 


 Eval vm_compute in List.nth 125 (fst c) _.

 Definition s126 := Eval vm_compute in (step_checker s125 (List.nth 125 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s126. 


 Eval vm_compute in List.nth 126 (fst c) _.

 Definition s127 := Eval vm_compute in (step_checker s126 (List.nth 126 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s127. 


 Eval vm_compute in List.nth 127 (fst c) _.

 Definition s128 := Eval vm_compute in (step_checker s127 (List.nth 127 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s128. 


 Eval vm_compute in List.nth 128 (fst c) _.

 Definition s129 := Eval vm_compute in (step_checker s128 (List.nth 128 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s129. 


 Eval vm_compute in List.nth 129 (fst c) _.

 Definition s130 := Eval vm_compute in (step_checker s129 (List.nth 129 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s130. 


 Eval vm_compute in List.nth 130 (fst c) _.

 Definition s131 := Eval vm_compute in (step_checker s130 (List.nth 130 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s131. 


 Eval vm_compute in List.nth 131 (fst c) _.

 Definition s132 := Eval vm_compute in (step_checker s131 (List.nth 131 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s132. 


 Eval vm_compute in List.nth 132 (fst c) _.

 Definition s133 := Eval vm_compute in (step_checker s132 (List.nth 132 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s133. 


 Eval vm_compute in List.nth 133 (fst c) _.

 Definition s134 := Eval vm_compute in (step_checker s133 (List.nth 133 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s134. 


 Eval vm_compute in List.nth 134 (fst c) _.

 Definition s135 := Eval vm_compute in (step_checker s134 (List.nth 134 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s135. 


 Eval vm_compute in List.nth 135 (fst c) _.

 Definition s136 := Eval vm_compute in (step_checker s135 (List.nth 135 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s136. 


 Eval vm_compute in List.nth 136 (fst c) _.

 Definition s137 := Eval vm_compute in (step_checker s136 (List.nth 136 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s137. 


 Eval vm_compute in List.nth 137 (fst c) _.

 Definition s138 := Eval vm_compute in (step_checker s137 (List.nth 137 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s138. 


 Eval vm_compute in List.nth 138 (fst c) _.

 Definition s139 := Eval vm_compute in (step_checker s138 (List.nth 138 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s139. 


 Eval vm_compute in List.nth 139 (fst c) _.

 Definition s140 := Eval vm_compute in (step_checker s139 (List.nth 139 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s140. 


 Eval vm_compute in List.nth 140 (fst c) _.

 Definition s141 := Eval vm_compute in (step_checker s140 (List.nth 140 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s141. 


 Eval vm_compute in List.nth 141 (fst c) _.

 Definition s142 := Eval vm_compute in (step_checker s141 (List.nth 141 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s142. 


 Eval vm_compute in List.nth 142 (fst c) _.

 Definition s143 := Eval vm_compute in (step_checker s142 (List.nth 142 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s143. 


 Eval vm_compute in List.nth 143 (fst c) _.

 Definition s144 := Eval vm_compute in (step_checker s143 (List.nth 143 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s144. 


 Eval vm_compute in List.nth 144 (fst c) _.

 Definition s145 := Eval vm_compute in (step_checker s144 (List.nth 144 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s145. 


 Eval vm_compute in List.nth 145 (fst c) _.

 Definition s146 := Eval vm_compute in (step_checker s145 (List.nth 145 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s146. 


 Eval vm_compute in List.nth 146 (fst c) _.

 Definition s147 := Eval vm_compute in (step_checker s146 (List.nth 146 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s147. 


 Eval vm_compute in List.nth 147 (fst c) _.

 Definition s148 := Eval vm_compute in (step_checker s147 (List.nth 147 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s148. 


 Eval vm_compute in List.nth 148 (fst c) _.

 Definition s149 := Eval vm_compute in (step_checker s148 (List.nth 148 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s149. 


 Eval vm_compute in List.nth 149 (fst c) _.

 Definition s150 := Eval vm_compute in (step_checker s149 (List.nth 149 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s150. 


 Eval vm_compute in List.nth 150 (fst c) _.

 Definition s151 := Eval vm_compute in (step_checker s150 (List.nth 150 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s151. 


 Eval vm_compute in List.nth 151 (fst c) _.

 Definition s152 := Eval vm_compute in (step_checker s151 (List.nth 151 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s152. 


 Eval vm_compute in List.nth 152 (fst c) _.

 Definition s153 := Eval vm_compute in (step_checker s152 (List.nth 152 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s153. 


 Eval vm_compute in List.nth 153 (fst c) _.

 Definition s154 := Eval vm_compute in (step_checker s153 (List.nth 153 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s154. 


 Eval vm_compute in List.nth 154 (fst c) _.

 Definition s155 := Eval vm_compute in (step_checker s154 (List.nth 154 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s155. 


 Eval vm_compute in List.nth 155 (fst c) _.

 Definition s156 := Eval vm_compute in (step_checker s155 (List.nth 155 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s156. 


 Eval vm_compute in List.nth 156 (fst c) _.

 Definition s157 := Eval vm_compute in (step_checker s156 (List.nth 156 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s157. 


 Eval vm_compute in List.nth 157 (fst c) _.

 Definition s158 := Eval vm_compute in (step_checker s157 (List.nth 157 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s158. 


 Eval vm_compute in List.nth 158 (fst c) _.

 Definition s159 := Eval vm_compute in (step_checker s158 (List.nth 158 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s159. 


 Eval vm_compute in List.nth 159 (fst c) _.

 Definition s160 := Eval vm_compute in (step_checker s159 (List.nth 159 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s160. 


 Eval vm_compute in List.nth 160 (fst c) _.

 Definition s161 := Eval vm_compute in (step_checker s160 (List.nth 160 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s161. 


 Eval vm_compute in List.nth 161 (fst c) _.

 Definition s162 := Eval vm_compute in (step_checker s161 (List.nth 161 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s162. 


 Eval vm_compute in List.nth 162 (fst c) _.

 Definition s163 := Eval vm_compute in (step_checker s162 (List.nth 162 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s163. 


 Eval vm_compute in List.nth 163 (fst c) _.

 Definition s164 := Eval vm_compute in (step_checker s163 (List.nth 163 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s164. 


 Eval vm_compute in List.nth 164 (fst c) _.

 Definition s165 := Eval vm_compute in (step_checker s164 (List.nth 164 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s165. 


 Eval vm_compute in List.nth 165 (fst c) _.

 Definition s166 := Eval vm_compute in (step_checker s165 (List.nth 165 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s166. 


 Eval vm_compute in List.nth 166 (fst c) _.

 Definition s167 := Eval vm_compute in (step_checker s166 (List.nth 166 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s167. 


 Eval vm_compute in List.nth 167 (fst c) _.

 Definition s168 := Eval vm_compute in (step_checker s167 (List.nth 167 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s168. 


 Eval vm_compute in List.nth 168 (fst c) _.

 Definition s169 := Eval vm_compute in (step_checker s168 (List.nth 168 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s169. 


 Eval vm_compute in List.nth 169 (fst c) _.

 Definition s170 := Eval vm_compute in (step_checker s169 (List.nth 169 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s170. 


 Eval vm_compute in List.nth 170 (fst c) _.

 Definition s171 := Eval vm_compute in (step_checker s170 (List.nth 170 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s171. 


 Eval vm_compute in List.nth 171 (fst c) _.

 Definition s172 := Eval vm_compute in (step_checker s171 (List.nth 171 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s172. 


 Eval vm_compute in List.nth 172 (fst c) _.

 Definition s173 := Eval vm_compute in (step_checker s172 (List.nth 172 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s173. 


 Eval vm_compute in List.nth 173 (fst c) _.

 Definition s174 := Eval vm_compute in (step_checker s173 (List.nth 173 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s174. 


 Eval vm_compute in List.nth 174 (fst c) _.

 Definition s175 := Eval vm_compute in (step_checker s174 (List.nth 174 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s175. 


 Eval vm_compute in List.nth 175 (fst c) _.

 Definition s176 := Eval vm_compute in (step_checker s175 (List.nth 175 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s176. 


 Eval vm_compute in List.nth 176 (fst c) _.

 Definition s177 := Eval vm_compute in (step_checker s176 (List.nth 176 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s177. 


 Eval vm_compute in List.nth 177 (fst c) _.

 Definition s178 := Eval vm_compute in (step_checker s177 (List.nth 177 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s178. 


 Eval vm_compute in List.nth 178 (fst c) _.

 Definition s179 := Eval vm_compute in (step_checker s178 (List.nth 178 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s179. 


 Eval vm_compute in List.nth 179 (fst c) _.

 Definition s180 := Eval vm_compute in (step_checker s179 (List.nth 179 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s180. 


 Eval vm_compute in List.nth 180 (fst c) _.

 Definition s181 := Eval vm_compute in (step_checker s180 (List.nth 180 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s181. 


 Eval vm_compute in List.nth 181 (fst c) _.

 Definition s182 := Eval vm_compute in (step_checker s181 (List.nth 181 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s182. 


 Eval vm_compute in List.nth 182 (fst c) _.

 Definition s183 := Eval vm_compute in (step_checker s182 (List.nth 182 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s183. 


 Eval vm_compute in List.nth 183 (fst c) _.

 Definition s184 := Eval vm_compute in (step_checker s183 (List.nth 183 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s184. 


 Eval vm_compute in List.nth 184 (fst c) _.

 Definition s185 := Eval vm_compute in (step_checker s184 (List.nth 184 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s185. 


 Eval vm_compute in List.nth 185 (fst c) _.

 Definition s186 := Eval vm_compute in (step_checker s185 (List.nth 185 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s186. 


 Eval vm_compute in List.nth 186 (fst c) _.

 Definition s187 := Eval vm_compute in (step_checker s186 (List.nth 186 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s187. 


 Eval vm_compute in List.nth 187 (fst c) _.

 Definition s188 := Eval vm_compute in (step_checker s187 (List.nth 187 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s188. 


 Eval vm_compute in List.nth 188 (fst c) _.

 Definition s189 := Eval vm_compute in (step_checker s188 (List.nth 188 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s189. 


 Eval vm_compute in List.nth 189 (fst c) _.

 Definition s190 := Eval vm_compute in (step_checker s189 (List.nth 189 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s190. 


 Eval vm_compute in List.nth 190 (fst c) _.

 Definition s191 := Eval vm_compute in (step_checker s190 (List.nth 190 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s191. 


 Eval vm_compute in List.nth 191 (fst c) _.

 Definition s192 := Eval vm_compute in (step_checker s191 (List.nth 191 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s192. 


 Eval vm_compute in List.nth 192 (fst c) _.

 Definition s193 := Eval vm_compute in (step_checker s192 (List.nth 192 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s193. 


 Eval vm_compute in List.nth 193 (fst c) _.

 Definition s194 := Eval vm_compute in (step_checker s193 (List.nth 193 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s194. 


 Eval vm_compute in List.nth 194 (fst c) _.

 Definition s195 := Eval vm_compute in (step_checker s194 (List.nth 194 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s195. 


 Eval vm_compute in List.nth 195 (fst c) _.

 Definition s196 := Eval vm_compute in (step_checker s195 (List.nth 195 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s196. 


 Eval vm_compute in List.nth 196 (fst c) _.

 Definition s197 := Eval vm_compute in (step_checker s196 (List.nth 196 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s197. 


 Eval vm_compute in List.nth 197 (fst c) _.

 Definition s198 := Eval vm_compute in (step_checker s197 (List.nth 197 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s198. 


 Eval vm_compute in List.nth 198 (fst c) _.

 Definition s199 := Eval vm_compute in (step_checker s198 (List.nth 198 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s199. 


 Eval vm_compute in List.nth 199 (fst c) _.

 Definition s200 := Eval vm_compute in (step_checker s199 (List.nth 199 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s200. 


 Eval vm_compute in List.nth 200 (fst c) _.

 Definition s201 := Eval vm_compute in (step_checker s200 (List.nth 200 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s201. 


 Eval vm_compute in List.nth 201 (fst c) _.

 Definition s202 := Eval vm_compute in (step_checker s201 (List.nth 201 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s202. 


 Eval vm_compute in List.nth 202 (fst c) _.

 Definition s203 := Eval vm_compute in (step_checker s202 (List.nth 202 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s203. 


 Eval vm_compute in List.nth 203 (fst c) _.

 Definition s204 := Eval vm_compute in (step_checker s203 (List.nth 203 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s204. 


 Eval vm_compute in List.nth 204 (fst c) _.

 Definition s205 := Eval vm_compute in (step_checker s204 (List.nth 204 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s205. 


 Eval vm_compute in List.nth 205 (fst c) _.

 Definition s206 := Eval vm_compute in (step_checker s205 (List.nth 205 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s206. 


 Eval vm_compute in List.nth 206 (fst c) _.

 Definition s207 := Eval vm_compute in (step_checker s206 (List.nth 206 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s207. 


 Eval vm_compute in List.nth 207 (fst c) _.

 Definition s208 := Eval vm_compute in (step_checker s207 (List.nth 207 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s208. 


 Eval vm_compute in List.nth 208 (fst c) _.

 Definition s209 := Eval vm_compute in (step_checker s208 (List.nth 208 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s209. 


 Eval vm_compute in List.nth 209 (fst c) _.

 Definition s210 := Eval vm_compute in (step_checker s209 (List.nth 209 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s210. 


 Eval vm_compute in List.nth 210 (fst c) _.

 Definition s211 := Eval vm_compute in (step_checker s210 (List.nth 210 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s211. 


 Eval vm_compute in List.nth 211 (fst c) _.

 Definition s212 := Eval vm_compute in (step_checker s211 (List.nth 211 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s212. 


 Eval vm_compute in List.nth 212 (fst c) _.

 Definition s213 := Eval vm_compute in (step_checker s212 (List.nth 212 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s213. 


 Eval vm_compute in List.nth 213 (fst c) _.

 Definition s214 := Eval vm_compute in (step_checker s213 (List.nth 213 (fst c) (CTrue t_func t_atom t_form 0))). 
 Print s214. 

End test7veritrun.