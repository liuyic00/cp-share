From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths.
From ArithmeticCommon Require Import BitvectorFacts.
From Divider Require Import Stable Representation Slices.
Local Open Scope Z_scope.
Lemma unsigned_slice width offset bits : to_Zpos (take width (drop offset bits)) = normalize width (Z.shiftr (to_Zpos bits) (Z.of_nat offset)).
Proof. rewrite unsigned_take unsigned_drop. reflexivity. Qed.

Transparent word_21.
Lemma slice_shape_21 v : word_21 v = take 65 (drop 64 (word_20 v)).
Proof. unfold word_21, closed_21, expr_21, word_of_eval.
 change (drop 64 (take 129 (word_20 v)) = take 65 (drop 64 (word_20 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_21.
Lemma slice_integer_21 s i ghost : to_Zpos (word_21 (encoded_leaves s i ghost)) = normalize 65 (Z.shiftr (to_Zpos (word_20 (encoded_leaves s i ghost))) 64).
Proof. rewrite slice_shape_21. apply unsigned_slice. Qed.
Transparent word_22.
Lemma slice_shape_22 v : word_22 v = take 64 (drop 0 (word_20 v)).
Proof. unfold word_22, closed_22, expr_22, word_of_eval.
 change (drop 0 (take 64 (word_20 v)) = take 64 (drop 0 (word_20 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_22.
Lemma slice_integer_22 s i ghost : to_Zpos (word_22 (encoded_leaves s i ghost)) = normalize 64 (Z.shiftr (to_Zpos (word_20 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_22. apply unsigned_slice. Qed.
Transparent word_23.
Lemma slice_shape_23 v : word_23 v = take 1 (drop 63 (word_4 v)).
Proof. unfold word_23, closed_23, expr_23, word_of_eval.
 change (drop 63 (take 64 (word_4 v)) = take 1 (drop 63 (word_4 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_23.
Lemma slice_integer_23 s i ghost : to_Zpos (word_23 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_4 (encoded_leaves s i ghost))) 63).
Proof. rewrite slice_shape_23. apply unsigned_slice. Qed.
Transparent word_26.
Lemma slice_shape_26 v : word_26 v = take 64 (drop 0 (word_25 v)).
Proof. unfold word_26, closed_26, expr_26, word_of_eval.
 rewrite drop0. reflexivity. Qed.
Opaque word_26.
Lemma slice_integer_26 s i ghost : to_Zpos (word_26 (encoded_leaves s i ghost)) = normalize 64 (Z.shiftr (to_Zpos (word_25 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_26. apply unsigned_slice. Qed.
Transparent word_28.
Lemma slice_shape_28 v : word_28 v = take 1 (drop 63 (word_5 v)).
Proof. unfold word_28, closed_28, expr_28, word_of_eval.
 change (drop 63 (take 64 (word_5 v)) = take 1 (drop 63 (word_5 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_28.
Lemma slice_integer_28 s i ghost : to_Zpos (word_28 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_5 (encoded_leaves s i ghost))) 63).
Proof. rewrite slice_shape_28. apply unsigned_slice. Qed.
Transparent word_31.
Lemma slice_shape_31 v : word_31 v = take 64 (drop 0 (word_30 v)).
Proof. unfold word_31, closed_31, expr_31, word_of_eval.
 rewrite drop0. reflexivity. Qed.
Opaque word_31.
Lemma slice_integer_31 s i ghost : to_Zpos (word_31 (encoded_leaves s i ghost)) = normalize 64 (Z.shiftr (to_Zpos (word_30 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_31. apply unsigned_slice. Qed.
Transparent word_53.
Lemma slice_shape_53 v : word_53 v = take 32 (drop 32 (word_40 v)).
Proof. unfold word_53, closed_53, expr_53, word_of_eval.
 change (drop 32 (take 64 (word_40 v)) = take 32 (drop 32 (word_40 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_53.
Lemma slice_integer_53 s i ghost : to_Zpos (word_53 (encoded_leaves s i ghost)) = normalize 32 (Z.shiftr (to_Zpos (word_40 (encoded_leaves s i ghost))) 32).
Proof. rewrite slice_shape_53. apply unsigned_slice. Qed.
Transparent word_54.
Lemma slice_shape_54 v : word_54 v = take 32 (drop 0 (word_40 v)).
Proof. unfold word_54, closed_54, expr_54, word_of_eval.
 change (drop 0 (take 32 (word_40 v)) = take 32 (drop 0 (word_40 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_54.
Lemma slice_integer_54 s i ghost : to_Zpos (word_54 (encoded_leaves s i ghost)) = normalize 32 (Z.shiftr (to_Zpos (word_40 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_54. apply unsigned_slice. Qed.
Transparent word_56.
Lemma slice_shape_56 v : word_56 v = take 16 (drop 16 (word_53 v)).
Proof. unfold word_56, closed_56, expr_56, word_of_eval.
 change (drop 16 (take 32 (word_53 v)) = take 16 (drop 16 (word_53 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_56.
Lemma slice_integer_56 s i ghost : to_Zpos (word_56 (encoded_leaves s i ghost)) = normalize 16 (Z.shiftr (to_Zpos (word_53 (encoded_leaves s i ghost))) 16).
Proof. rewrite slice_shape_56. apply unsigned_slice. Qed.
Transparent word_57.
Lemma slice_shape_57 v : word_57 v = take 16 (drop 0 (word_53 v)).
Proof. unfold word_57, closed_57, expr_57, word_of_eval.
 change (drop 0 (take 16 (word_53 v)) = take 16 (drop 0 (word_53 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_57.
Lemma slice_integer_57 s i ghost : to_Zpos (word_57 (encoded_leaves s i ghost)) = normalize 16 (Z.shiftr (to_Zpos (word_53 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_57. apply unsigned_slice. Qed.
Transparent word_59.
Lemma slice_shape_59 v : word_59 v = take 8 (drop 8 (word_56 v)).
Proof. unfold word_59, closed_59, expr_59, word_of_eval.
 change (drop 8 (take 16 (word_56 v)) = take 8 (drop 8 (word_56 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_59.
Lemma slice_integer_59 s i ghost : to_Zpos (word_59 (encoded_leaves s i ghost)) = normalize 8 (Z.shiftr (to_Zpos (word_56 (encoded_leaves s i ghost))) 8).
Proof. rewrite slice_shape_59. apply unsigned_slice. Qed.
Transparent word_60.
Lemma slice_shape_60 v : word_60 v = take 8 (drop 0 (word_56 v)).
Proof. unfold word_60, closed_60, expr_60, word_of_eval.
 change (drop 0 (take 8 (word_56 v)) = take 8 (drop 0 (word_56 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_60.
Lemma slice_integer_60 s i ghost : to_Zpos (word_60 (encoded_leaves s i ghost)) = normalize 8 (Z.shiftr (to_Zpos (word_56 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_60. apply unsigned_slice. Qed.
Transparent word_62.
Lemma slice_shape_62 v : word_62 v = take 4 (drop 4 (word_59 v)).
Proof. unfold word_62, closed_62, expr_62, word_of_eval.
 change (drop 4 (take 8 (word_59 v)) = take 4 (drop 4 (word_59 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_62.
Lemma slice_integer_62 s i ghost : to_Zpos (word_62 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_59 (encoded_leaves s i ghost))) 4).
Proof. rewrite slice_shape_62. apply unsigned_slice. Qed.
Transparent word_63.
Lemma slice_shape_63 v : word_63 v = take 4 (drop 0 (word_59 v)).
Proof. unfold word_63, closed_63, expr_63, word_of_eval.
 change (drop 0 (take 4 (word_59 v)) = take 4 (drop 0 (word_59 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_63.
Lemma slice_integer_63 s i ghost : to_Zpos (word_63 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_59 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_63. apply unsigned_slice. Qed.
Transparent word_65.
Lemma slice_shape_65 v : word_65 v = take 1 (drop 3 (word_62 v)).
Proof. unfold word_65, closed_65, expr_65, word_of_eval.
 change (drop 3 (take 4 (word_62 v)) = take 1 (drop 3 (word_62 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_65.
Lemma slice_integer_65 s i ghost : to_Zpos (word_65 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_62 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_65. apply unsigned_slice. Qed.
Transparent word_66.
Lemma slice_shape_66 v : word_66 v = take 1 (drop 2 (word_62 v)).
Proof. unfold word_66, closed_66, expr_66, word_of_eval.
 change (drop 2 (take 3 (word_62 v)) = take 1 (drop 2 (word_62 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_66.
Lemma slice_integer_66 s i ghost : to_Zpos (word_66 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_62 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_66. apply unsigned_slice. Qed.
Transparent word_67.
Lemma slice_shape_67 v : word_67 v = take 1 (drop 1 (word_62 v)).
Proof. unfold word_67, closed_67, expr_67, word_of_eval.
 change (drop 1 (take 2 (word_62 v)) = take 1 (drop 1 (word_62 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_67.
Lemma slice_integer_67 s i ghost : to_Zpos (word_67 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_62 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_67. apply unsigned_slice. Qed.
Transparent word_70.
Lemma slice_shape_70 v : word_70 v = take 1 (drop 3 (word_63 v)).
Proof. unfold word_70, closed_70, expr_70, word_of_eval.
 change (drop 3 (take 4 (word_63 v)) = take 1 (drop 3 (word_63 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_70.
Lemma slice_integer_70 s i ghost : to_Zpos (word_70 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_63 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_70. apply unsigned_slice. Qed.
Transparent word_71.
Lemma slice_shape_71 v : word_71 v = take 1 (drop 2 (word_63 v)).
Proof. unfold word_71, closed_71, expr_71, word_of_eval.
 change (drop 2 (take 3 (word_63 v)) = take 1 (drop 2 (word_63 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_71.
Lemma slice_integer_71 s i ghost : to_Zpos (word_71 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_63 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_71. apply unsigned_slice. Qed.
Transparent word_72.
Lemma slice_shape_72 v : word_72 v = take 1 (drop 1 (word_63 v)).
Proof. unfold word_72, closed_72, expr_72, word_of_eval.
 change (drop 1 (take 2 (word_63 v)) = take 1 (drop 1 (word_63 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_72.
Lemma slice_integer_72 s i ghost : to_Zpos (word_72 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_63 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_72. apply unsigned_slice. Qed.
Transparent word_77.
Lemma slice_shape_77 v : word_77 v = take 4 (drop 4 (word_60 v)).
Proof. unfold word_77, closed_77, expr_77, word_of_eval.
 change (drop 4 (take 8 (word_60 v)) = take 4 (drop 4 (word_60 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_77.
Lemma slice_integer_77 s i ghost : to_Zpos (word_77 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_60 (encoded_leaves s i ghost))) 4).
Proof. rewrite slice_shape_77. apply unsigned_slice. Qed.
Transparent word_78.
Lemma slice_shape_78 v : word_78 v = take 4 (drop 0 (word_60 v)).
Proof. unfold word_78, closed_78, expr_78, word_of_eval.
 change (drop 0 (take 4 (word_60 v)) = take 4 (drop 0 (word_60 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_78.
Lemma slice_integer_78 s i ghost : to_Zpos (word_78 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_60 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_78. apply unsigned_slice. Qed.
Transparent word_80.
Lemma slice_shape_80 v : word_80 v = take 1 (drop 3 (word_77 v)).
Proof. unfold word_80, closed_80, expr_80, word_of_eval.
 change (drop 3 (take 4 (word_77 v)) = take 1 (drop 3 (word_77 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_80.
Lemma slice_integer_80 s i ghost : to_Zpos (word_80 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_77 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_80. apply unsigned_slice. Qed.
Transparent word_81.
Lemma slice_shape_81 v : word_81 v = take 1 (drop 2 (word_77 v)).
Proof. unfold word_81, closed_81, expr_81, word_of_eval.
 change (drop 2 (take 3 (word_77 v)) = take 1 (drop 2 (word_77 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_81.
Lemma slice_integer_81 s i ghost : to_Zpos (word_81 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_77 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_81. apply unsigned_slice. Qed.
Transparent word_82.
Lemma slice_shape_82 v : word_82 v = take 1 (drop 1 (word_77 v)).
Proof. unfold word_82, closed_82, expr_82, word_of_eval.
 change (drop 1 (take 2 (word_77 v)) = take 1 (drop 1 (word_77 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_82.
Lemma slice_integer_82 s i ghost : to_Zpos (word_82 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_77 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_82. apply unsigned_slice. Qed.
Transparent word_85.
Lemma slice_shape_85 v : word_85 v = take 1 (drop 3 (word_78 v)).
Proof. unfold word_85, closed_85, expr_85, word_of_eval.
 change (drop 3 (take 4 (word_78 v)) = take 1 (drop 3 (word_78 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_85.
Lemma slice_integer_85 s i ghost : to_Zpos (word_85 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_78 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_85. apply unsigned_slice. Qed.
Transparent word_86.
Lemma slice_shape_86 v : word_86 v = take 1 (drop 2 (word_78 v)).
Proof. unfold word_86, closed_86, expr_86, word_of_eval.
 change (drop 2 (take 3 (word_78 v)) = take 1 (drop 2 (word_78 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_86.
Lemma slice_integer_86 s i ghost : to_Zpos (word_86 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_78 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_86. apply unsigned_slice. Qed.
Transparent word_87.
Lemma slice_shape_87 v : word_87 v = take 1 (drop 1 (word_78 v)).
Proof. unfold word_87, closed_87, expr_87, word_of_eval.
 change (drop 1 (take 2 (word_78 v)) = take 1 (drop 1 (word_78 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_87.
Lemma slice_integer_87 s i ghost : to_Zpos (word_87 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_78 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_87. apply unsigned_slice. Qed.
Transparent word_94.
Lemma slice_shape_94 v : word_94 v = take 8 (drop 8 (word_57 v)).
Proof. unfold word_94, closed_94, expr_94, word_of_eval.
 change (drop 8 (take 16 (word_57 v)) = take 8 (drop 8 (word_57 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_94.
Lemma slice_integer_94 s i ghost : to_Zpos (word_94 (encoded_leaves s i ghost)) = normalize 8 (Z.shiftr (to_Zpos (word_57 (encoded_leaves s i ghost))) 8).
Proof. rewrite slice_shape_94. apply unsigned_slice. Qed.
Transparent word_95.
Lemma slice_shape_95 v : word_95 v = take 8 (drop 0 (word_57 v)).
Proof. unfold word_95, closed_95, expr_95, word_of_eval.
 change (drop 0 (take 8 (word_57 v)) = take 8 (drop 0 (word_57 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_95.
Lemma slice_integer_95 s i ghost : to_Zpos (word_95 (encoded_leaves s i ghost)) = normalize 8 (Z.shiftr (to_Zpos (word_57 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_95. apply unsigned_slice. Qed.
Transparent word_97.
Lemma slice_shape_97 v : word_97 v = take 4 (drop 4 (word_94 v)).
Proof. unfold word_97, closed_97, expr_97, word_of_eval.
 change (drop 4 (take 8 (word_94 v)) = take 4 (drop 4 (word_94 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_97.
Lemma slice_integer_97 s i ghost : to_Zpos (word_97 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_94 (encoded_leaves s i ghost))) 4).
Proof. rewrite slice_shape_97. apply unsigned_slice. Qed.
Transparent word_98.
Lemma slice_shape_98 v : word_98 v = take 4 (drop 0 (word_94 v)).
Proof. unfold word_98, closed_98, expr_98, word_of_eval.
 change (drop 0 (take 4 (word_94 v)) = take 4 (drop 0 (word_94 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_98.
Lemma slice_integer_98 s i ghost : to_Zpos (word_98 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_94 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_98. apply unsigned_slice. Qed.
Transparent word_100.
Lemma slice_shape_100 v : word_100 v = take 1 (drop 3 (word_97 v)).
Proof. unfold word_100, closed_100, expr_100, word_of_eval.
 change (drop 3 (take 4 (word_97 v)) = take 1 (drop 3 (word_97 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_100.
Lemma slice_integer_100 s i ghost : to_Zpos (word_100 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_97 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_100. apply unsigned_slice. Qed.
Transparent word_101.
Lemma slice_shape_101 v : word_101 v = take 1 (drop 2 (word_97 v)).
Proof. unfold word_101, closed_101, expr_101, word_of_eval.
 change (drop 2 (take 3 (word_97 v)) = take 1 (drop 2 (word_97 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_101.
Lemma slice_integer_101 s i ghost : to_Zpos (word_101 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_97 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_101. apply unsigned_slice. Qed.
Transparent word_102.
Lemma slice_shape_102 v : word_102 v = take 1 (drop 1 (word_97 v)).
Proof. unfold word_102, closed_102, expr_102, word_of_eval.
 change (drop 1 (take 2 (word_97 v)) = take 1 (drop 1 (word_97 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_102.
Lemma slice_integer_102 s i ghost : to_Zpos (word_102 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_97 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_102. apply unsigned_slice. Qed.
Transparent word_105.
Lemma slice_shape_105 v : word_105 v = take 1 (drop 3 (word_98 v)).
Proof. unfold word_105, closed_105, expr_105, word_of_eval.
 change (drop 3 (take 4 (word_98 v)) = take 1 (drop 3 (word_98 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_105.
Lemma slice_integer_105 s i ghost : to_Zpos (word_105 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_98 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_105. apply unsigned_slice. Qed.
Transparent word_106.
Lemma slice_shape_106 v : word_106 v = take 1 (drop 2 (word_98 v)).
Proof. unfold word_106, closed_106, expr_106, word_of_eval.
 change (drop 2 (take 3 (word_98 v)) = take 1 (drop 2 (word_98 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_106.
Lemma slice_integer_106 s i ghost : to_Zpos (word_106 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_98 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_106. apply unsigned_slice. Qed.
Transparent word_107.
Lemma slice_shape_107 v : word_107 v = take 1 (drop 1 (word_98 v)).
Proof. unfold word_107, closed_107, expr_107, word_of_eval.
 change (drop 1 (take 2 (word_98 v)) = take 1 (drop 1 (word_98 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_107.
Lemma slice_integer_107 s i ghost : to_Zpos (word_107 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_98 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_107. apply unsigned_slice. Qed.
Transparent word_112.
Lemma slice_shape_112 v : word_112 v = take 4 (drop 4 (word_95 v)).
Proof. unfold word_112, closed_112, expr_112, word_of_eval.
 change (drop 4 (take 8 (word_95 v)) = take 4 (drop 4 (word_95 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_112.
Lemma slice_integer_112 s i ghost : to_Zpos (word_112 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_95 (encoded_leaves s i ghost))) 4).
Proof. rewrite slice_shape_112. apply unsigned_slice. Qed.
Transparent word_113.
Lemma slice_shape_113 v : word_113 v = take 4 (drop 0 (word_95 v)).
Proof. unfold word_113, closed_113, expr_113, word_of_eval.
 change (drop 0 (take 4 (word_95 v)) = take 4 (drop 0 (word_95 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_113.
Lemma slice_integer_113 s i ghost : to_Zpos (word_113 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_95 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_113. apply unsigned_slice. Qed.
Transparent word_115.
Lemma slice_shape_115 v : word_115 v = take 1 (drop 3 (word_112 v)).
Proof. unfold word_115, closed_115, expr_115, word_of_eval.
 change (drop 3 (take 4 (word_112 v)) = take 1 (drop 3 (word_112 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_115.
Lemma slice_integer_115 s i ghost : to_Zpos (word_115 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_112 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_115. apply unsigned_slice. Qed.
Transparent word_116.
Lemma slice_shape_116 v : word_116 v = take 1 (drop 2 (word_112 v)).
Proof. unfold word_116, closed_116, expr_116, word_of_eval.
 change (drop 2 (take 3 (word_112 v)) = take 1 (drop 2 (word_112 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_116.
Lemma slice_integer_116 s i ghost : to_Zpos (word_116 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_112 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_116. apply unsigned_slice. Qed.
Transparent word_117.
Lemma slice_shape_117 v : word_117 v = take 1 (drop 1 (word_112 v)).
Proof. unfold word_117, closed_117, expr_117, word_of_eval.
 change (drop 1 (take 2 (word_112 v)) = take 1 (drop 1 (word_112 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_117.
Lemma slice_integer_117 s i ghost : to_Zpos (word_117 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_112 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_117. apply unsigned_slice. Qed.
Transparent word_120.
Lemma slice_shape_120 v : word_120 v = take 1 (drop 3 (word_113 v)).
Proof. unfold word_120, closed_120, expr_120, word_of_eval.
 change (drop 3 (take 4 (word_113 v)) = take 1 (drop 3 (word_113 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_120.
Lemma slice_integer_120 s i ghost : to_Zpos (word_120 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_113 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_120. apply unsigned_slice. Qed.
Transparent word_121.
Lemma slice_shape_121 v : word_121 v = take 1 (drop 2 (word_113 v)).
Proof. unfold word_121, closed_121, expr_121, word_of_eval.
 change (drop 2 (take 3 (word_113 v)) = take 1 (drop 2 (word_113 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_121.
Lemma slice_integer_121 s i ghost : to_Zpos (word_121 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_113 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_121. apply unsigned_slice. Qed.
Transparent word_122.
Lemma slice_shape_122 v : word_122 v = take 1 (drop 1 (word_113 v)).
Proof. unfold word_122, closed_122, expr_122, word_of_eval.
 change (drop 1 (take 2 (word_113 v)) = take 1 (drop 1 (word_113 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_122.
Lemma slice_integer_122 s i ghost : to_Zpos (word_122 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_113 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_122. apply unsigned_slice. Qed.
Transparent word_131.
Lemma slice_shape_131 v : word_131 v = take 16 (drop 16 (word_54 v)).
Proof. unfold word_131, closed_131, expr_131, word_of_eval.
 change (drop 16 (take 32 (word_54 v)) = take 16 (drop 16 (word_54 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_131.
Lemma slice_integer_131 s i ghost : to_Zpos (word_131 (encoded_leaves s i ghost)) = normalize 16 (Z.shiftr (to_Zpos (word_54 (encoded_leaves s i ghost))) 16).
Proof. rewrite slice_shape_131. apply unsigned_slice. Qed.
Transparent word_132.
Lemma slice_shape_132 v : word_132 v = take 16 (drop 0 (word_54 v)).
Proof. unfold word_132, closed_132, expr_132, word_of_eval.
 change (drop 0 (take 16 (word_54 v)) = take 16 (drop 0 (word_54 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_132.
Lemma slice_integer_132 s i ghost : to_Zpos (word_132 (encoded_leaves s i ghost)) = normalize 16 (Z.shiftr (to_Zpos (word_54 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_132. apply unsigned_slice. Qed.
Transparent word_134.
Lemma slice_shape_134 v : word_134 v = take 8 (drop 8 (word_131 v)).
Proof. unfold word_134, closed_134, expr_134, word_of_eval.
 change (drop 8 (take 16 (word_131 v)) = take 8 (drop 8 (word_131 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_134.
Lemma slice_integer_134 s i ghost : to_Zpos (word_134 (encoded_leaves s i ghost)) = normalize 8 (Z.shiftr (to_Zpos (word_131 (encoded_leaves s i ghost))) 8).
Proof. rewrite slice_shape_134. apply unsigned_slice. Qed.
Transparent word_135.
Lemma slice_shape_135 v : word_135 v = take 8 (drop 0 (word_131 v)).
Proof. unfold word_135, closed_135, expr_135, word_of_eval.
 change (drop 0 (take 8 (word_131 v)) = take 8 (drop 0 (word_131 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_135.
Lemma slice_integer_135 s i ghost : to_Zpos (word_135 (encoded_leaves s i ghost)) = normalize 8 (Z.shiftr (to_Zpos (word_131 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_135. apply unsigned_slice. Qed.
Transparent word_137.
Lemma slice_shape_137 v : word_137 v = take 4 (drop 4 (word_134 v)).
Proof. unfold word_137, closed_137, expr_137, word_of_eval.
 change (drop 4 (take 8 (word_134 v)) = take 4 (drop 4 (word_134 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_137.
Lemma slice_integer_137 s i ghost : to_Zpos (word_137 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_134 (encoded_leaves s i ghost))) 4).
Proof. rewrite slice_shape_137. apply unsigned_slice. Qed.
Transparent word_138.
Lemma slice_shape_138 v : word_138 v = take 4 (drop 0 (word_134 v)).
Proof. unfold word_138, closed_138, expr_138, word_of_eval.
 change (drop 0 (take 4 (word_134 v)) = take 4 (drop 0 (word_134 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_138.
Lemma slice_integer_138 s i ghost : to_Zpos (word_138 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_134 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_138. apply unsigned_slice. Qed.
Transparent word_140.
Lemma slice_shape_140 v : word_140 v = take 1 (drop 3 (word_137 v)).
Proof. unfold word_140, closed_140, expr_140, word_of_eval.
 change (drop 3 (take 4 (word_137 v)) = take 1 (drop 3 (word_137 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_140.
Lemma slice_integer_140 s i ghost : to_Zpos (word_140 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_137 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_140. apply unsigned_slice. Qed.
Transparent word_141.
Lemma slice_shape_141 v : word_141 v = take 1 (drop 2 (word_137 v)).
Proof. unfold word_141, closed_141, expr_141, word_of_eval.
 change (drop 2 (take 3 (word_137 v)) = take 1 (drop 2 (word_137 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_141.
Lemma slice_integer_141 s i ghost : to_Zpos (word_141 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_137 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_141. apply unsigned_slice. Qed.
Transparent word_142.
Lemma slice_shape_142 v : word_142 v = take 1 (drop 1 (word_137 v)).
Proof. unfold word_142, closed_142, expr_142, word_of_eval.
 change (drop 1 (take 2 (word_137 v)) = take 1 (drop 1 (word_137 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_142.
Lemma slice_integer_142 s i ghost : to_Zpos (word_142 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_137 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_142. apply unsigned_slice. Qed.
Transparent word_145.
Lemma slice_shape_145 v : word_145 v = take 1 (drop 3 (word_138 v)).
Proof. unfold word_145, closed_145, expr_145, word_of_eval.
 change (drop 3 (take 4 (word_138 v)) = take 1 (drop 3 (word_138 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_145.
Lemma slice_integer_145 s i ghost : to_Zpos (word_145 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_138 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_145. apply unsigned_slice. Qed.
Transparent word_146.
Lemma slice_shape_146 v : word_146 v = take 1 (drop 2 (word_138 v)).
Proof. unfold word_146, closed_146, expr_146, word_of_eval.
 change (drop 2 (take 3 (word_138 v)) = take 1 (drop 2 (word_138 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_146.
Lemma slice_integer_146 s i ghost : to_Zpos (word_146 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_138 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_146. apply unsigned_slice. Qed.
Transparent word_147.
Lemma slice_shape_147 v : word_147 v = take 1 (drop 1 (word_138 v)).
Proof. unfold word_147, closed_147, expr_147, word_of_eval.
 change (drop 1 (take 2 (word_138 v)) = take 1 (drop 1 (word_138 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_147.
Lemma slice_integer_147 s i ghost : to_Zpos (word_147 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_138 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_147. apply unsigned_slice. Qed.
Transparent word_152.
Lemma slice_shape_152 v : word_152 v = take 4 (drop 4 (word_135 v)).
Proof. unfold word_152, closed_152, expr_152, word_of_eval.
 change (drop 4 (take 8 (word_135 v)) = take 4 (drop 4 (word_135 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_152.
Lemma slice_integer_152 s i ghost : to_Zpos (word_152 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_135 (encoded_leaves s i ghost))) 4).
Proof. rewrite slice_shape_152. apply unsigned_slice. Qed.
Transparent word_153.
Lemma slice_shape_153 v : word_153 v = take 4 (drop 0 (word_135 v)).
Proof. unfold word_153, closed_153, expr_153, word_of_eval.
 change (drop 0 (take 4 (word_135 v)) = take 4 (drop 0 (word_135 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_153.
Lemma slice_integer_153 s i ghost : to_Zpos (word_153 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_135 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_153. apply unsigned_slice. Qed.
Transparent word_155.
Lemma slice_shape_155 v : word_155 v = take 1 (drop 3 (word_152 v)).
Proof. unfold word_155, closed_155, expr_155, word_of_eval.
 change (drop 3 (take 4 (word_152 v)) = take 1 (drop 3 (word_152 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_155.
Lemma slice_integer_155 s i ghost : to_Zpos (word_155 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_152 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_155. apply unsigned_slice. Qed.
Transparent word_156.
Lemma slice_shape_156 v : word_156 v = take 1 (drop 2 (word_152 v)).
Proof. unfold word_156, closed_156, expr_156, word_of_eval.
 change (drop 2 (take 3 (word_152 v)) = take 1 (drop 2 (word_152 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_156.
Lemma slice_integer_156 s i ghost : to_Zpos (word_156 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_152 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_156. apply unsigned_slice. Qed.
Transparent word_157.
Lemma slice_shape_157 v : word_157 v = take 1 (drop 1 (word_152 v)).
Proof. unfold word_157, closed_157, expr_157, word_of_eval.
 change (drop 1 (take 2 (word_152 v)) = take 1 (drop 1 (word_152 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_157.
Lemma slice_integer_157 s i ghost : to_Zpos (word_157 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_152 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_157. apply unsigned_slice. Qed.
Transparent word_160.
Lemma slice_shape_160 v : word_160 v = take 1 (drop 3 (word_153 v)).
Proof. unfold word_160, closed_160, expr_160, word_of_eval.
 change (drop 3 (take 4 (word_153 v)) = take 1 (drop 3 (word_153 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_160.
Lemma slice_integer_160 s i ghost : to_Zpos (word_160 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_153 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_160. apply unsigned_slice. Qed.
Transparent word_161.
Lemma slice_shape_161 v : word_161 v = take 1 (drop 2 (word_153 v)).
Proof. unfold word_161, closed_161, expr_161, word_of_eval.
 change (drop 2 (take 3 (word_153 v)) = take 1 (drop 2 (word_153 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_161.
Lemma slice_integer_161 s i ghost : to_Zpos (word_161 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_153 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_161. apply unsigned_slice. Qed.
Transparent word_162.
Lemma slice_shape_162 v : word_162 v = take 1 (drop 1 (word_153 v)).
Proof. unfold word_162, closed_162, expr_162, word_of_eval.
 change (drop 1 (take 2 (word_153 v)) = take 1 (drop 1 (word_153 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_162.
Lemma slice_integer_162 s i ghost : to_Zpos (word_162 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_153 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_162. apply unsigned_slice. Qed.
Transparent word_169.
Lemma slice_shape_169 v : word_169 v = take 8 (drop 8 (word_132 v)).
Proof. unfold word_169, closed_169, expr_169, word_of_eval.
 change (drop 8 (take 16 (word_132 v)) = take 8 (drop 8 (word_132 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_169.
Lemma slice_integer_169 s i ghost : to_Zpos (word_169 (encoded_leaves s i ghost)) = normalize 8 (Z.shiftr (to_Zpos (word_132 (encoded_leaves s i ghost))) 8).
Proof. rewrite slice_shape_169. apply unsigned_slice. Qed.
Transparent word_170.
Lemma slice_shape_170 v : word_170 v = take 8 (drop 0 (word_132 v)).
Proof. unfold word_170, closed_170, expr_170, word_of_eval.
 change (drop 0 (take 8 (word_132 v)) = take 8 (drop 0 (word_132 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_170.
Lemma slice_integer_170 s i ghost : to_Zpos (word_170 (encoded_leaves s i ghost)) = normalize 8 (Z.shiftr (to_Zpos (word_132 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_170. apply unsigned_slice. Qed.
Transparent word_172.
Lemma slice_shape_172 v : word_172 v = take 4 (drop 4 (word_169 v)).
Proof. unfold word_172, closed_172, expr_172, word_of_eval.
 change (drop 4 (take 8 (word_169 v)) = take 4 (drop 4 (word_169 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_172.
Lemma slice_integer_172 s i ghost : to_Zpos (word_172 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_169 (encoded_leaves s i ghost))) 4).
Proof. rewrite slice_shape_172. apply unsigned_slice. Qed.
Transparent word_173.
Lemma slice_shape_173 v : word_173 v = take 4 (drop 0 (word_169 v)).
Proof. unfold word_173, closed_173, expr_173, word_of_eval.
 change (drop 0 (take 4 (word_169 v)) = take 4 (drop 0 (word_169 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_173.
Lemma slice_integer_173 s i ghost : to_Zpos (word_173 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_169 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_173. apply unsigned_slice. Qed.
Transparent word_175.
Lemma slice_shape_175 v : word_175 v = take 1 (drop 3 (word_172 v)).
Proof. unfold word_175, closed_175, expr_175, word_of_eval.
 change (drop 3 (take 4 (word_172 v)) = take 1 (drop 3 (word_172 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_175.
Lemma slice_integer_175 s i ghost : to_Zpos (word_175 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_172 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_175. apply unsigned_slice. Qed.
Transparent word_176.
Lemma slice_shape_176 v : word_176 v = take 1 (drop 2 (word_172 v)).
Proof. unfold word_176, closed_176, expr_176, word_of_eval.
 change (drop 2 (take 3 (word_172 v)) = take 1 (drop 2 (word_172 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_176.
Lemma slice_integer_176 s i ghost : to_Zpos (word_176 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_172 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_176. apply unsigned_slice. Qed.
Transparent word_177.
Lemma slice_shape_177 v : word_177 v = take 1 (drop 1 (word_172 v)).
Proof. unfold word_177, closed_177, expr_177, word_of_eval.
 change (drop 1 (take 2 (word_172 v)) = take 1 (drop 1 (word_172 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_177.
Lemma slice_integer_177 s i ghost : to_Zpos (word_177 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_172 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_177. apply unsigned_slice. Qed.
Transparent word_180.
Lemma slice_shape_180 v : word_180 v = take 1 (drop 3 (word_173 v)).
Proof. unfold word_180, closed_180, expr_180, word_of_eval.
 change (drop 3 (take 4 (word_173 v)) = take 1 (drop 3 (word_173 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_180.
Lemma slice_integer_180 s i ghost : to_Zpos (word_180 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_173 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_180. apply unsigned_slice. Qed.
Transparent word_181.
Lemma slice_shape_181 v : word_181 v = take 1 (drop 2 (word_173 v)).
Proof. unfold word_181, closed_181, expr_181, word_of_eval.
 change (drop 2 (take 3 (word_173 v)) = take 1 (drop 2 (word_173 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_181.
Lemma slice_integer_181 s i ghost : to_Zpos (word_181 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_173 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_181. apply unsigned_slice. Qed.
Transparent word_182.
Lemma slice_shape_182 v : word_182 v = take 1 (drop 1 (word_173 v)).
Proof. unfold word_182, closed_182, expr_182, word_of_eval.
 change (drop 1 (take 2 (word_173 v)) = take 1 (drop 1 (word_173 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_182.
Lemma slice_integer_182 s i ghost : to_Zpos (word_182 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_173 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_182. apply unsigned_slice. Qed.
Transparent word_187.
Lemma slice_shape_187 v : word_187 v = take 4 (drop 4 (word_170 v)).
Proof. unfold word_187, closed_187, expr_187, word_of_eval.
 change (drop 4 (take 8 (word_170 v)) = take 4 (drop 4 (word_170 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_187.
Lemma slice_integer_187 s i ghost : to_Zpos (word_187 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_170 (encoded_leaves s i ghost))) 4).
Proof. rewrite slice_shape_187. apply unsigned_slice. Qed.
Transparent word_188.
Lemma slice_shape_188 v : word_188 v = take 4 (drop 0 (word_170 v)).
Proof. unfold word_188, closed_188, expr_188, word_of_eval.
 change (drop 0 (take 4 (word_170 v)) = take 4 (drop 0 (word_170 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_188.
Lemma slice_integer_188 s i ghost : to_Zpos (word_188 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_170 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_188. apply unsigned_slice. Qed.
Transparent word_190.
Lemma slice_shape_190 v : word_190 v = take 1 (drop 3 (word_187 v)).
Proof. unfold word_190, closed_190, expr_190, word_of_eval.
 change (drop 3 (take 4 (word_187 v)) = take 1 (drop 3 (word_187 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_190.
Lemma slice_integer_190 s i ghost : to_Zpos (word_190 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_187 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_190. apply unsigned_slice. Qed.
Transparent word_191.
Lemma slice_shape_191 v : word_191 v = take 1 (drop 2 (word_187 v)).
Proof. unfold word_191, closed_191, expr_191, word_of_eval.
 change (drop 2 (take 3 (word_187 v)) = take 1 (drop 2 (word_187 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_191.
Lemma slice_integer_191 s i ghost : to_Zpos (word_191 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_187 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_191. apply unsigned_slice. Qed.
Transparent word_192.
Lemma slice_shape_192 v : word_192 v = take 1 (drop 1 (word_187 v)).
Proof. unfold word_192, closed_192, expr_192, word_of_eval.
 change (drop 1 (take 2 (word_187 v)) = take 1 (drop 1 (word_187 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_192.
Lemma slice_integer_192 s i ghost : to_Zpos (word_192 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_187 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_192. apply unsigned_slice. Qed.
Transparent word_195.
Lemma slice_shape_195 v : word_195 v = take 1 (drop 3 (word_188 v)).
Proof. unfold word_195, closed_195, expr_195, word_of_eval.
 change (drop 3 (take 4 (word_188 v)) = take 1 (drop 3 (word_188 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_195.
Lemma slice_integer_195 s i ghost : to_Zpos (word_195 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_188 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_195. apply unsigned_slice. Qed.
Transparent word_196.
Lemma slice_shape_196 v : word_196 v = take 1 (drop 2 (word_188 v)).
Proof. unfold word_196, closed_196, expr_196, word_of_eval.
 change (drop 2 (take 3 (word_188 v)) = take 1 (drop 2 (word_188 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_196.
Lemma slice_integer_196 s i ghost : to_Zpos (word_196 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_188 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_196. apply unsigned_slice. Qed.
Transparent word_197.
Lemma slice_shape_197 v : word_197 v = take 1 (drop 1 (word_188 v)).
Proof. unfold word_197, closed_197, expr_197, word_of_eval.
 change (drop 1 (take 2 (word_188 v)) = take 1 (drop 1 (word_188 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_197.
Lemma slice_integer_197 s i ghost : to_Zpos (word_197 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_188 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_197. apply unsigned_slice. Qed.
Transparent word_209.
Lemma slice_shape_209 v : word_209 v = take 7 (drop 0 (word_208 v)).
Proof. unfold word_209, closed_209, expr_209, word_of_eval.
 rewrite drop0. reflexivity. Qed.
Opaque word_209.
Lemma slice_integer_209 s i ghost : to_Zpos (word_209 (encoded_leaves s i ghost)) = normalize 7 (Z.shiftr (to_Zpos (word_208 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_209. apply unsigned_slice. Qed.
Transparent word_210.
Lemma slice_shape_210 v : word_210 v = take 1 (drop 64 (word_43 v)).
Proof. unfold word_210, closed_210, expr_210, word_of_eval.
 change (drop 64 (take 65 (word_43 v)) = take 1 (drop 64 (word_43 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_210.
Lemma slice_integer_210 s i ghost : to_Zpos (word_210 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_43 (encoded_leaves s i ghost))) 64).
Proof. rewrite slice_shape_210. apply unsigned_slice. Qed.
Transparent word_211.
Lemma slice_shape_211 v : word_211 v = take 64 (drop 0 (word_43 v)).
Proof. unfold word_211, closed_211, expr_211, word_of_eval.
 change (drop 0 (take 64 (word_43 v)) = take 64 (drop 0 (word_43 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_211.
Lemma slice_integer_211 s i ghost : to_Zpos (word_211 (encoded_leaves s i ghost)) = normalize 64 (Z.shiftr (to_Zpos (word_43 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_211. apply unsigned_slice. Qed.
Transparent word_213.
Lemma slice_shape_213 v : word_213 v = take 32 (drop 32 (word_211 v)).
Proof. unfold word_213, closed_213, expr_213, word_of_eval.
 change (drop 32 (take 64 (word_211 v)) = take 32 (drop 32 (word_211 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_213.
Lemma slice_integer_213 s i ghost : to_Zpos (word_213 (encoded_leaves s i ghost)) = normalize 32 (Z.shiftr (to_Zpos (word_211 (encoded_leaves s i ghost))) 32).
Proof. rewrite slice_shape_213. apply unsigned_slice. Qed.
Transparent word_214.
Lemma slice_shape_214 v : word_214 v = take 32 (drop 0 (word_211 v)).
Proof. unfold word_214, closed_214, expr_214, word_of_eval.
 change (drop 0 (take 32 (word_211 v)) = take 32 (drop 0 (word_211 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_214.
Lemma slice_integer_214 s i ghost : to_Zpos (word_214 (encoded_leaves s i ghost)) = normalize 32 (Z.shiftr (to_Zpos (word_211 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_214. apply unsigned_slice. Qed.
Transparent word_216.
Lemma slice_shape_216 v : word_216 v = take 16 (drop 16 (word_213 v)).
Proof. unfold word_216, closed_216, expr_216, word_of_eval.
 change (drop 16 (take 32 (word_213 v)) = take 16 (drop 16 (word_213 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_216.
Lemma slice_integer_216 s i ghost : to_Zpos (word_216 (encoded_leaves s i ghost)) = normalize 16 (Z.shiftr (to_Zpos (word_213 (encoded_leaves s i ghost))) 16).
Proof. rewrite slice_shape_216. apply unsigned_slice. Qed.
Transparent word_217.
Lemma slice_shape_217 v : word_217 v = take 16 (drop 0 (word_213 v)).
Proof. unfold word_217, closed_217, expr_217, word_of_eval.
 change (drop 0 (take 16 (word_213 v)) = take 16 (drop 0 (word_213 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_217.
Lemma slice_integer_217 s i ghost : to_Zpos (word_217 (encoded_leaves s i ghost)) = normalize 16 (Z.shiftr (to_Zpos (word_213 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_217. apply unsigned_slice. Qed.
Transparent word_219.
Lemma slice_shape_219 v : word_219 v = take 8 (drop 8 (word_216 v)).
Proof. unfold word_219, closed_219, expr_219, word_of_eval.
 change (drop 8 (take 16 (word_216 v)) = take 8 (drop 8 (word_216 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_219.
Lemma slice_integer_219 s i ghost : to_Zpos (word_219 (encoded_leaves s i ghost)) = normalize 8 (Z.shiftr (to_Zpos (word_216 (encoded_leaves s i ghost))) 8).
Proof. rewrite slice_shape_219. apply unsigned_slice. Qed.
Transparent word_220.
Lemma slice_shape_220 v : word_220 v = take 8 (drop 0 (word_216 v)).
Proof. unfold word_220, closed_220, expr_220, word_of_eval.
 change (drop 0 (take 8 (word_216 v)) = take 8 (drop 0 (word_216 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_220.
Lemma slice_integer_220 s i ghost : to_Zpos (word_220 (encoded_leaves s i ghost)) = normalize 8 (Z.shiftr (to_Zpos (word_216 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_220. apply unsigned_slice. Qed.
Transparent word_222.
Lemma slice_shape_222 v : word_222 v = take 4 (drop 4 (word_219 v)).
Proof. unfold word_222, closed_222, expr_222, word_of_eval.
 change (drop 4 (take 8 (word_219 v)) = take 4 (drop 4 (word_219 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_222.
Lemma slice_integer_222 s i ghost : to_Zpos (word_222 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_219 (encoded_leaves s i ghost))) 4).
Proof. rewrite slice_shape_222. apply unsigned_slice. Qed.
Transparent word_223.
Lemma slice_shape_223 v : word_223 v = take 4 (drop 0 (word_219 v)).
Proof. unfold word_223, closed_223, expr_223, word_of_eval.
 change (drop 0 (take 4 (word_219 v)) = take 4 (drop 0 (word_219 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_223.
Lemma slice_integer_223 s i ghost : to_Zpos (word_223 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_219 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_223. apply unsigned_slice. Qed.
Transparent word_225.
Lemma slice_shape_225 v : word_225 v = take 1 (drop 3 (word_222 v)).
Proof. unfold word_225, closed_225, expr_225, word_of_eval.
 change (drop 3 (take 4 (word_222 v)) = take 1 (drop 3 (word_222 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_225.
Lemma slice_integer_225 s i ghost : to_Zpos (word_225 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_222 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_225. apply unsigned_slice. Qed.
Transparent word_226.
Lemma slice_shape_226 v : word_226 v = take 1 (drop 2 (word_222 v)).
Proof. unfold word_226, closed_226, expr_226, word_of_eval.
 change (drop 2 (take 3 (word_222 v)) = take 1 (drop 2 (word_222 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_226.
Lemma slice_integer_226 s i ghost : to_Zpos (word_226 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_222 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_226. apply unsigned_slice. Qed.
Transparent word_227.
Lemma slice_shape_227 v : word_227 v = take 1 (drop 1 (word_222 v)).
Proof. unfold word_227, closed_227, expr_227, word_of_eval.
 change (drop 1 (take 2 (word_222 v)) = take 1 (drop 1 (word_222 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_227.
Lemma slice_integer_227 s i ghost : to_Zpos (word_227 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_222 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_227. apply unsigned_slice. Qed.
Transparent word_230.
Lemma slice_shape_230 v : word_230 v = take 1 (drop 3 (word_223 v)).
Proof. unfold word_230, closed_230, expr_230, word_of_eval.
 change (drop 3 (take 4 (word_223 v)) = take 1 (drop 3 (word_223 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_230.
Lemma slice_integer_230 s i ghost : to_Zpos (word_230 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_223 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_230. apply unsigned_slice. Qed.
Transparent word_231.
Lemma slice_shape_231 v : word_231 v = take 1 (drop 2 (word_223 v)).
Proof. unfold word_231, closed_231, expr_231, word_of_eval.
 change (drop 2 (take 3 (word_223 v)) = take 1 (drop 2 (word_223 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_231.
Lemma slice_integer_231 s i ghost : to_Zpos (word_231 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_223 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_231. apply unsigned_slice. Qed.
Transparent word_232.
Lemma slice_shape_232 v : word_232 v = take 1 (drop 1 (word_223 v)).
Proof. unfold word_232, closed_232, expr_232, word_of_eval.
 change (drop 1 (take 2 (word_223 v)) = take 1 (drop 1 (word_223 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_232.
Lemma slice_integer_232 s i ghost : to_Zpos (word_232 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_223 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_232. apply unsigned_slice. Qed.
Transparent word_237.
Lemma slice_shape_237 v : word_237 v = take 4 (drop 4 (word_220 v)).
Proof. unfold word_237, closed_237, expr_237, word_of_eval.
 change (drop 4 (take 8 (word_220 v)) = take 4 (drop 4 (word_220 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_237.
Lemma slice_integer_237 s i ghost : to_Zpos (word_237 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_220 (encoded_leaves s i ghost))) 4).
Proof. rewrite slice_shape_237. apply unsigned_slice. Qed.
Transparent word_238.
Lemma slice_shape_238 v : word_238 v = take 4 (drop 0 (word_220 v)).
Proof. unfold word_238, closed_238, expr_238, word_of_eval.
 change (drop 0 (take 4 (word_220 v)) = take 4 (drop 0 (word_220 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_238.
Lemma slice_integer_238 s i ghost : to_Zpos (word_238 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_220 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_238. apply unsigned_slice. Qed.
Transparent word_240.
Lemma slice_shape_240 v : word_240 v = take 1 (drop 3 (word_237 v)).
Proof. unfold word_240, closed_240, expr_240, word_of_eval.
 change (drop 3 (take 4 (word_237 v)) = take 1 (drop 3 (word_237 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_240.
Lemma slice_integer_240 s i ghost : to_Zpos (word_240 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_237 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_240. apply unsigned_slice. Qed.
Transparent word_241.
Lemma slice_shape_241 v : word_241 v = take 1 (drop 2 (word_237 v)).
Proof. unfold word_241, closed_241, expr_241, word_of_eval.
 change (drop 2 (take 3 (word_237 v)) = take 1 (drop 2 (word_237 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_241.
Lemma slice_integer_241 s i ghost : to_Zpos (word_241 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_237 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_241. apply unsigned_slice. Qed.
Transparent word_242.
Lemma slice_shape_242 v : word_242 v = take 1 (drop 1 (word_237 v)).
Proof. unfold word_242, closed_242, expr_242, word_of_eval.
 change (drop 1 (take 2 (word_237 v)) = take 1 (drop 1 (word_237 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_242.
Lemma slice_integer_242 s i ghost : to_Zpos (word_242 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_237 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_242. apply unsigned_slice. Qed.
Transparent word_245.
Lemma slice_shape_245 v : word_245 v = take 1 (drop 3 (word_238 v)).
Proof. unfold word_245, closed_245, expr_245, word_of_eval.
 change (drop 3 (take 4 (word_238 v)) = take 1 (drop 3 (word_238 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_245.
Lemma slice_integer_245 s i ghost : to_Zpos (word_245 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_238 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_245. apply unsigned_slice. Qed.
Transparent word_246.
Lemma slice_shape_246 v : word_246 v = take 1 (drop 2 (word_238 v)).
Proof. unfold word_246, closed_246, expr_246, word_of_eval.
 change (drop 2 (take 3 (word_238 v)) = take 1 (drop 2 (word_238 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_246.
Lemma slice_integer_246 s i ghost : to_Zpos (word_246 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_238 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_246. apply unsigned_slice. Qed.
Transparent word_247.
Lemma slice_shape_247 v : word_247 v = take 1 (drop 1 (word_238 v)).
Proof. unfold word_247, closed_247, expr_247, word_of_eval.
 change (drop 1 (take 2 (word_238 v)) = take 1 (drop 1 (word_238 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_247.
Lemma slice_integer_247 s i ghost : to_Zpos (word_247 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_238 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_247. apply unsigned_slice. Qed.
Transparent word_254.
Lemma slice_shape_254 v : word_254 v = take 8 (drop 8 (word_217 v)).
Proof. unfold word_254, closed_254, expr_254, word_of_eval.
 change (drop 8 (take 16 (word_217 v)) = take 8 (drop 8 (word_217 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_254.
Lemma slice_integer_254 s i ghost : to_Zpos (word_254 (encoded_leaves s i ghost)) = normalize 8 (Z.shiftr (to_Zpos (word_217 (encoded_leaves s i ghost))) 8).
Proof. rewrite slice_shape_254. apply unsigned_slice. Qed.
Transparent word_255.
Lemma slice_shape_255 v : word_255 v = take 8 (drop 0 (word_217 v)).
Proof. unfold word_255, closed_255, expr_255, word_of_eval.
 change (drop 0 (take 8 (word_217 v)) = take 8 (drop 0 (word_217 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_255.
Lemma slice_integer_255 s i ghost : to_Zpos (word_255 (encoded_leaves s i ghost)) = normalize 8 (Z.shiftr (to_Zpos (word_217 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_255. apply unsigned_slice. Qed.
Transparent word_257.
Lemma slice_shape_257 v : word_257 v = take 4 (drop 4 (word_254 v)).
Proof. unfold word_257, closed_257, expr_257, word_of_eval.
 change (drop 4 (take 8 (word_254 v)) = take 4 (drop 4 (word_254 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_257.
Lemma slice_integer_257 s i ghost : to_Zpos (word_257 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_254 (encoded_leaves s i ghost))) 4).
Proof. rewrite slice_shape_257. apply unsigned_slice. Qed.
Transparent word_258.
Lemma slice_shape_258 v : word_258 v = take 4 (drop 0 (word_254 v)).
Proof. unfold word_258, closed_258, expr_258, word_of_eval.
 change (drop 0 (take 4 (word_254 v)) = take 4 (drop 0 (word_254 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_258.
Lemma slice_integer_258 s i ghost : to_Zpos (word_258 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_254 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_258. apply unsigned_slice. Qed.
Transparent word_260.
Lemma slice_shape_260 v : word_260 v = take 1 (drop 3 (word_257 v)).
Proof. unfold word_260, closed_260, expr_260, word_of_eval.
 change (drop 3 (take 4 (word_257 v)) = take 1 (drop 3 (word_257 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_260.
Lemma slice_integer_260 s i ghost : to_Zpos (word_260 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_257 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_260. apply unsigned_slice. Qed.
Transparent word_261.
Lemma slice_shape_261 v : word_261 v = take 1 (drop 2 (word_257 v)).
Proof. unfold word_261, closed_261, expr_261, word_of_eval.
 change (drop 2 (take 3 (word_257 v)) = take 1 (drop 2 (word_257 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_261.
Lemma slice_integer_261 s i ghost : to_Zpos (word_261 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_257 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_261. apply unsigned_slice. Qed.
Transparent word_262.
Lemma slice_shape_262 v : word_262 v = take 1 (drop 1 (word_257 v)).
Proof. unfold word_262, closed_262, expr_262, word_of_eval.
 change (drop 1 (take 2 (word_257 v)) = take 1 (drop 1 (word_257 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_262.
Lemma slice_integer_262 s i ghost : to_Zpos (word_262 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_257 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_262. apply unsigned_slice. Qed.
Transparent word_265.
Lemma slice_shape_265 v : word_265 v = take 1 (drop 3 (word_258 v)).
Proof. unfold word_265, closed_265, expr_265, word_of_eval.
 change (drop 3 (take 4 (word_258 v)) = take 1 (drop 3 (word_258 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_265.
Lemma slice_integer_265 s i ghost : to_Zpos (word_265 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_258 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_265. apply unsigned_slice. Qed.
Transparent word_266.
Lemma slice_shape_266 v : word_266 v = take 1 (drop 2 (word_258 v)).
Proof. unfold word_266, closed_266, expr_266, word_of_eval.
 change (drop 2 (take 3 (word_258 v)) = take 1 (drop 2 (word_258 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_266.
Lemma slice_integer_266 s i ghost : to_Zpos (word_266 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_258 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_266. apply unsigned_slice. Qed.
Transparent word_267.
Lemma slice_shape_267 v : word_267 v = take 1 (drop 1 (word_258 v)).
Proof. unfold word_267, closed_267, expr_267, word_of_eval.
 change (drop 1 (take 2 (word_258 v)) = take 1 (drop 1 (word_258 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_267.
Lemma slice_integer_267 s i ghost : to_Zpos (word_267 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_258 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_267. apply unsigned_slice. Qed.
Transparent word_272.
Lemma slice_shape_272 v : word_272 v = take 4 (drop 4 (word_255 v)).
Proof. unfold word_272, closed_272, expr_272, word_of_eval.
 change (drop 4 (take 8 (word_255 v)) = take 4 (drop 4 (word_255 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_272.
Lemma slice_integer_272 s i ghost : to_Zpos (word_272 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_255 (encoded_leaves s i ghost))) 4).
Proof. rewrite slice_shape_272. apply unsigned_slice. Qed.
Transparent word_273.
Lemma slice_shape_273 v : word_273 v = take 4 (drop 0 (word_255 v)).
Proof. unfold word_273, closed_273, expr_273, word_of_eval.
 change (drop 0 (take 4 (word_255 v)) = take 4 (drop 0 (word_255 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_273.
Lemma slice_integer_273 s i ghost : to_Zpos (word_273 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_255 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_273. apply unsigned_slice. Qed.
Transparent word_275.
Lemma slice_shape_275 v : word_275 v = take 1 (drop 3 (word_272 v)).
Proof. unfold word_275, closed_275, expr_275, word_of_eval.
 change (drop 3 (take 4 (word_272 v)) = take 1 (drop 3 (word_272 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_275.
Lemma slice_integer_275 s i ghost : to_Zpos (word_275 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_272 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_275. apply unsigned_slice. Qed.
Transparent word_276.
Lemma slice_shape_276 v : word_276 v = take 1 (drop 2 (word_272 v)).
Proof. unfold word_276, closed_276, expr_276, word_of_eval.
 change (drop 2 (take 3 (word_272 v)) = take 1 (drop 2 (word_272 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_276.
Lemma slice_integer_276 s i ghost : to_Zpos (word_276 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_272 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_276. apply unsigned_slice. Qed.
Transparent word_277.
Lemma slice_shape_277 v : word_277 v = take 1 (drop 1 (word_272 v)).
Proof. unfold word_277, closed_277, expr_277, word_of_eval.
 change (drop 1 (take 2 (word_272 v)) = take 1 (drop 1 (word_272 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_277.
Lemma slice_integer_277 s i ghost : to_Zpos (word_277 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_272 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_277. apply unsigned_slice. Qed.
Transparent word_280.
Lemma slice_shape_280 v : word_280 v = take 1 (drop 3 (word_273 v)).
Proof. unfold word_280, closed_280, expr_280, word_of_eval.
 change (drop 3 (take 4 (word_273 v)) = take 1 (drop 3 (word_273 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_280.
Lemma slice_integer_280 s i ghost : to_Zpos (word_280 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_273 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_280. apply unsigned_slice. Qed.
Transparent word_281.
Lemma slice_shape_281 v : word_281 v = take 1 (drop 2 (word_273 v)).
Proof. unfold word_281, closed_281, expr_281, word_of_eval.
 change (drop 2 (take 3 (word_273 v)) = take 1 (drop 2 (word_273 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_281.
Lemma slice_integer_281 s i ghost : to_Zpos (word_281 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_273 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_281. apply unsigned_slice. Qed.
Transparent word_282.
Lemma slice_shape_282 v : word_282 v = take 1 (drop 1 (word_273 v)).
Proof. unfold word_282, closed_282, expr_282, word_of_eval.
 change (drop 1 (take 2 (word_273 v)) = take 1 (drop 1 (word_273 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_282.
Lemma slice_integer_282 s i ghost : to_Zpos (word_282 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_273 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_282. apply unsigned_slice. Qed.
Transparent word_291.
Lemma slice_shape_291 v : word_291 v = take 16 (drop 16 (word_214 v)).
Proof. unfold word_291, closed_291, expr_291, word_of_eval.
 change (drop 16 (take 32 (word_214 v)) = take 16 (drop 16 (word_214 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_291.
Lemma slice_integer_291 s i ghost : to_Zpos (word_291 (encoded_leaves s i ghost)) = normalize 16 (Z.shiftr (to_Zpos (word_214 (encoded_leaves s i ghost))) 16).
Proof. rewrite slice_shape_291. apply unsigned_slice. Qed.
Transparent word_292.
Lemma slice_shape_292 v : word_292 v = take 16 (drop 0 (word_214 v)).
Proof. unfold word_292, closed_292, expr_292, word_of_eval.
 change (drop 0 (take 16 (word_214 v)) = take 16 (drop 0 (word_214 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_292.
Lemma slice_integer_292 s i ghost : to_Zpos (word_292 (encoded_leaves s i ghost)) = normalize 16 (Z.shiftr (to_Zpos (word_214 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_292. apply unsigned_slice. Qed.
Transparent word_294.
Lemma slice_shape_294 v : word_294 v = take 8 (drop 8 (word_291 v)).
Proof. unfold word_294, closed_294, expr_294, word_of_eval.
 change (drop 8 (take 16 (word_291 v)) = take 8 (drop 8 (word_291 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_294.
Lemma slice_integer_294 s i ghost : to_Zpos (word_294 (encoded_leaves s i ghost)) = normalize 8 (Z.shiftr (to_Zpos (word_291 (encoded_leaves s i ghost))) 8).
Proof. rewrite slice_shape_294. apply unsigned_slice. Qed.
Transparent word_295.
Lemma slice_shape_295 v : word_295 v = take 8 (drop 0 (word_291 v)).
Proof. unfold word_295, closed_295, expr_295, word_of_eval.
 change (drop 0 (take 8 (word_291 v)) = take 8 (drop 0 (word_291 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_295.
Lemma slice_integer_295 s i ghost : to_Zpos (word_295 (encoded_leaves s i ghost)) = normalize 8 (Z.shiftr (to_Zpos (word_291 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_295. apply unsigned_slice. Qed.
Transparent word_297.
Lemma slice_shape_297 v : word_297 v = take 4 (drop 4 (word_294 v)).
Proof. unfold word_297, closed_297, expr_297, word_of_eval.
 change (drop 4 (take 8 (word_294 v)) = take 4 (drop 4 (word_294 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_297.
Lemma slice_integer_297 s i ghost : to_Zpos (word_297 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_294 (encoded_leaves s i ghost))) 4).
Proof. rewrite slice_shape_297. apply unsigned_slice. Qed.
Transparent word_298.
Lemma slice_shape_298 v : word_298 v = take 4 (drop 0 (word_294 v)).
Proof. unfold word_298, closed_298, expr_298, word_of_eval.
 change (drop 0 (take 4 (word_294 v)) = take 4 (drop 0 (word_294 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_298.
Lemma slice_integer_298 s i ghost : to_Zpos (word_298 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_294 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_298. apply unsigned_slice. Qed.
Transparent word_300.
Lemma slice_shape_300 v : word_300 v = take 1 (drop 3 (word_297 v)).
Proof. unfold word_300, closed_300, expr_300, word_of_eval.
 change (drop 3 (take 4 (word_297 v)) = take 1 (drop 3 (word_297 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_300.
Lemma slice_integer_300 s i ghost : to_Zpos (word_300 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_297 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_300. apply unsigned_slice. Qed.
Transparent word_301.
Lemma slice_shape_301 v : word_301 v = take 1 (drop 2 (word_297 v)).
Proof. unfold word_301, closed_301, expr_301, word_of_eval.
 change (drop 2 (take 3 (word_297 v)) = take 1 (drop 2 (word_297 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_301.
Lemma slice_integer_301 s i ghost : to_Zpos (word_301 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_297 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_301. apply unsigned_slice. Qed.
Transparent word_302.
Lemma slice_shape_302 v : word_302 v = take 1 (drop 1 (word_297 v)).
Proof. unfold word_302, closed_302, expr_302, word_of_eval.
 change (drop 1 (take 2 (word_297 v)) = take 1 (drop 1 (word_297 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_302.
Lemma slice_integer_302 s i ghost : to_Zpos (word_302 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_297 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_302. apply unsigned_slice. Qed.
Transparent word_305.
Lemma slice_shape_305 v : word_305 v = take 1 (drop 3 (word_298 v)).
Proof. unfold word_305, closed_305, expr_305, word_of_eval.
 change (drop 3 (take 4 (word_298 v)) = take 1 (drop 3 (word_298 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_305.
Lemma slice_integer_305 s i ghost : to_Zpos (word_305 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_298 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_305. apply unsigned_slice. Qed.
Transparent word_306.
Lemma slice_shape_306 v : word_306 v = take 1 (drop 2 (word_298 v)).
Proof. unfold word_306, closed_306, expr_306, word_of_eval.
 change (drop 2 (take 3 (word_298 v)) = take 1 (drop 2 (word_298 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_306.
Lemma slice_integer_306 s i ghost : to_Zpos (word_306 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_298 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_306. apply unsigned_slice. Qed.
Transparent word_307.
Lemma slice_shape_307 v : word_307 v = take 1 (drop 1 (word_298 v)).
Proof. unfold word_307, closed_307, expr_307, word_of_eval.
 change (drop 1 (take 2 (word_298 v)) = take 1 (drop 1 (word_298 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_307.
Lemma slice_integer_307 s i ghost : to_Zpos (word_307 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_298 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_307. apply unsigned_slice. Qed.
Transparent word_312.
Lemma slice_shape_312 v : word_312 v = take 4 (drop 4 (word_295 v)).
Proof. unfold word_312, closed_312, expr_312, word_of_eval.
 change (drop 4 (take 8 (word_295 v)) = take 4 (drop 4 (word_295 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_312.
Lemma slice_integer_312 s i ghost : to_Zpos (word_312 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_295 (encoded_leaves s i ghost))) 4).
Proof. rewrite slice_shape_312. apply unsigned_slice. Qed.
Transparent word_313.
Lemma slice_shape_313 v : word_313 v = take 4 (drop 0 (word_295 v)).
Proof. unfold word_313, closed_313, expr_313, word_of_eval.
 change (drop 0 (take 4 (word_295 v)) = take 4 (drop 0 (word_295 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_313.
Lemma slice_integer_313 s i ghost : to_Zpos (word_313 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_295 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_313. apply unsigned_slice. Qed.
Transparent word_315.
Lemma slice_shape_315 v : word_315 v = take 1 (drop 3 (word_312 v)).
Proof. unfold word_315, closed_315, expr_315, word_of_eval.
 change (drop 3 (take 4 (word_312 v)) = take 1 (drop 3 (word_312 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_315.
Lemma slice_integer_315 s i ghost : to_Zpos (word_315 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_312 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_315. apply unsigned_slice. Qed.
Transparent word_316.
Lemma slice_shape_316 v : word_316 v = take 1 (drop 2 (word_312 v)).
Proof. unfold word_316, closed_316, expr_316, word_of_eval.
 change (drop 2 (take 3 (word_312 v)) = take 1 (drop 2 (word_312 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_316.
Lemma slice_integer_316 s i ghost : to_Zpos (word_316 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_312 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_316. apply unsigned_slice. Qed.
Transparent word_317.
Lemma slice_shape_317 v : word_317 v = take 1 (drop 1 (word_312 v)).
Proof. unfold word_317, closed_317, expr_317, word_of_eval.
 change (drop 1 (take 2 (word_312 v)) = take 1 (drop 1 (word_312 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_317.
Lemma slice_integer_317 s i ghost : to_Zpos (word_317 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_312 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_317. apply unsigned_slice. Qed.
Transparent word_320.
Lemma slice_shape_320 v : word_320 v = take 1 (drop 3 (word_313 v)).
Proof. unfold word_320, closed_320, expr_320, word_of_eval.
 change (drop 3 (take 4 (word_313 v)) = take 1 (drop 3 (word_313 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_320.
Lemma slice_integer_320 s i ghost : to_Zpos (word_320 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_313 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_320. apply unsigned_slice. Qed.
Transparent word_321.
Lemma slice_shape_321 v : word_321 v = take 1 (drop 2 (word_313 v)).
Proof. unfold word_321, closed_321, expr_321, word_of_eval.
 change (drop 2 (take 3 (word_313 v)) = take 1 (drop 2 (word_313 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_321.
Lemma slice_integer_321 s i ghost : to_Zpos (word_321 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_313 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_321. apply unsigned_slice. Qed.
Transparent word_322.
Lemma slice_shape_322 v : word_322 v = take 1 (drop 1 (word_313 v)).
Proof. unfold word_322, closed_322, expr_322, word_of_eval.
 change (drop 1 (take 2 (word_313 v)) = take 1 (drop 1 (word_313 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_322.
Lemma slice_integer_322 s i ghost : to_Zpos (word_322 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_313 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_322. apply unsigned_slice. Qed.
Transparent word_329.
Lemma slice_shape_329 v : word_329 v = take 8 (drop 8 (word_292 v)).
Proof. unfold word_329, closed_329, expr_329, word_of_eval.
 change (drop 8 (take 16 (word_292 v)) = take 8 (drop 8 (word_292 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_329.
Lemma slice_integer_329 s i ghost : to_Zpos (word_329 (encoded_leaves s i ghost)) = normalize 8 (Z.shiftr (to_Zpos (word_292 (encoded_leaves s i ghost))) 8).
Proof. rewrite slice_shape_329. apply unsigned_slice. Qed.
Transparent word_330.
Lemma slice_shape_330 v : word_330 v = take 8 (drop 0 (word_292 v)).
Proof. unfold word_330, closed_330, expr_330, word_of_eval.
 change (drop 0 (take 8 (word_292 v)) = take 8 (drop 0 (word_292 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_330.
Lemma slice_integer_330 s i ghost : to_Zpos (word_330 (encoded_leaves s i ghost)) = normalize 8 (Z.shiftr (to_Zpos (word_292 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_330. apply unsigned_slice. Qed.
Transparent word_332.
Lemma slice_shape_332 v : word_332 v = take 4 (drop 4 (word_329 v)).
Proof. unfold word_332, closed_332, expr_332, word_of_eval.
 change (drop 4 (take 8 (word_329 v)) = take 4 (drop 4 (word_329 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_332.
Lemma slice_integer_332 s i ghost : to_Zpos (word_332 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_329 (encoded_leaves s i ghost))) 4).
Proof. rewrite slice_shape_332. apply unsigned_slice. Qed.
Transparent word_333.
Lemma slice_shape_333 v : word_333 v = take 4 (drop 0 (word_329 v)).
Proof. unfold word_333, closed_333, expr_333, word_of_eval.
 change (drop 0 (take 4 (word_329 v)) = take 4 (drop 0 (word_329 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_333.
Lemma slice_integer_333 s i ghost : to_Zpos (word_333 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_329 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_333. apply unsigned_slice. Qed.
Transparent word_335.
Lemma slice_shape_335 v : word_335 v = take 1 (drop 3 (word_332 v)).
Proof. unfold word_335, closed_335, expr_335, word_of_eval.
 change (drop 3 (take 4 (word_332 v)) = take 1 (drop 3 (word_332 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_335.
Lemma slice_integer_335 s i ghost : to_Zpos (word_335 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_332 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_335. apply unsigned_slice. Qed.
Transparent word_336.
Lemma slice_shape_336 v : word_336 v = take 1 (drop 2 (word_332 v)).
Proof. unfold word_336, closed_336, expr_336, word_of_eval.
 change (drop 2 (take 3 (word_332 v)) = take 1 (drop 2 (word_332 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_336.
Lemma slice_integer_336 s i ghost : to_Zpos (word_336 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_332 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_336. apply unsigned_slice. Qed.
Transparent word_337.
Lemma slice_shape_337 v : word_337 v = take 1 (drop 1 (word_332 v)).
Proof. unfold word_337, closed_337, expr_337, word_of_eval.
 change (drop 1 (take 2 (word_332 v)) = take 1 (drop 1 (word_332 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_337.
Lemma slice_integer_337 s i ghost : to_Zpos (word_337 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_332 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_337. apply unsigned_slice. Qed.
Transparent word_340.
Lemma slice_shape_340 v : word_340 v = take 1 (drop 3 (word_333 v)).
Proof. unfold word_340, closed_340, expr_340, word_of_eval.
 change (drop 3 (take 4 (word_333 v)) = take 1 (drop 3 (word_333 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_340.
Lemma slice_integer_340 s i ghost : to_Zpos (word_340 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_333 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_340. apply unsigned_slice. Qed.
Transparent word_341.
Lemma slice_shape_341 v : word_341 v = take 1 (drop 2 (word_333 v)).
Proof. unfold word_341, closed_341, expr_341, word_of_eval.
 change (drop 2 (take 3 (word_333 v)) = take 1 (drop 2 (word_333 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_341.
Lemma slice_integer_341 s i ghost : to_Zpos (word_341 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_333 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_341. apply unsigned_slice. Qed.
Transparent word_342.
Lemma slice_shape_342 v : word_342 v = take 1 (drop 1 (word_333 v)).
Proof. unfold word_342, closed_342, expr_342, word_of_eval.
 change (drop 1 (take 2 (word_333 v)) = take 1 (drop 1 (word_333 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_342.
Lemma slice_integer_342 s i ghost : to_Zpos (word_342 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_333 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_342. apply unsigned_slice. Qed.
Transparent word_347.
Lemma slice_shape_347 v : word_347 v = take 4 (drop 4 (word_330 v)).
Proof. unfold word_347, closed_347, expr_347, word_of_eval.
 change (drop 4 (take 8 (word_330 v)) = take 4 (drop 4 (word_330 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_347.
Lemma slice_integer_347 s i ghost : to_Zpos (word_347 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_330 (encoded_leaves s i ghost))) 4).
Proof. rewrite slice_shape_347. apply unsigned_slice. Qed.
Transparent word_348.
Lemma slice_shape_348 v : word_348 v = take 4 (drop 0 (word_330 v)).
Proof. unfold word_348, closed_348, expr_348, word_of_eval.
 change (drop 0 (take 4 (word_330 v)) = take 4 (drop 0 (word_330 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_348.
Lemma slice_integer_348 s i ghost : to_Zpos (word_348 (encoded_leaves s i ghost)) = normalize 4 (Z.shiftr (to_Zpos (word_330 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_348. apply unsigned_slice. Qed.
Transparent word_350.
Lemma slice_shape_350 v : word_350 v = take 1 (drop 3 (word_347 v)).
Proof. unfold word_350, closed_350, expr_350, word_of_eval.
 change (drop 3 (take 4 (word_347 v)) = take 1 (drop 3 (word_347 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_350.
Lemma slice_integer_350 s i ghost : to_Zpos (word_350 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_347 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_350. apply unsigned_slice. Qed.
Transparent word_351.
Lemma slice_shape_351 v : word_351 v = take 1 (drop 2 (word_347 v)).
Proof. unfold word_351, closed_351, expr_351, word_of_eval.
 change (drop 2 (take 3 (word_347 v)) = take 1 (drop 2 (word_347 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_351.
Lemma slice_integer_351 s i ghost : to_Zpos (word_351 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_347 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_351. apply unsigned_slice. Qed.
Transparent word_352.
Lemma slice_shape_352 v : word_352 v = take 1 (drop 1 (word_347 v)).
Proof. unfold word_352, closed_352, expr_352, word_of_eval.
 change (drop 1 (take 2 (word_347 v)) = take 1 (drop 1 (word_347 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_352.
Lemma slice_integer_352 s i ghost : to_Zpos (word_352 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_347 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_352. apply unsigned_slice. Qed.
Transparent word_355.
Lemma slice_shape_355 v : word_355 v = take 1 (drop 3 (word_348 v)).
Proof. unfold word_355, closed_355, expr_355, word_of_eval.
 change (drop 3 (take 4 (word_348 v)) = take 1 (drop 3 (word_348 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_355.
Lemma slice_integer_355 s i ghost : to_Zpos (word_355 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_348 (encoded_leaves s i ghost))) 3).
Proof. rewrite slice_shape_355. apply unsigned_slice. Qed.
Transparent word_356.
Lemma slice_shape_356 v : word_356 v = take 1 (drop 2 (word_348 v)).
Proof. unfold word_356, closed_356, expr_356, word_of_eval.
 change (drop 2 (take 3 (word_348 v)) = take 1 (drop 2 (word_348 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_356.
Lemma slice_integer_356 s i ghost : to_Zpos (word_356 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_348 (encoded_leaves s i ghost))) 2).
Proof. rewrite slice_shape_356. apply unsigned_slice. Qed.
Transparent word_357.
Lemma slice_shape_357 v : word_357 v = take 1 (drop 1 (word_348 v)).
Proof. unfold word_357, closed_357, expr_357, word_of_eval.
 change (drop 1 (take 2 (word_348 v)) = take 1 (drop 1 (word_348 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_357.
Lemma slice_integer_357 s i ghost : to_Zpos (word_357 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_348 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_357. apply unsigned_slice. Qed.
Transparent word_371.
Lemma slice_shape_371 v : word_371 v = take 7 (drop 0 (word_370 v)).
Proof. unfold word_371, closed_371, expr_371, word_of_eval.
 rewrite drop0. reflexivity. Qed.
Opaque word_371.
Lemma slice_integer_371 s i ghost : to_Zpos (word_371 (encoded_leaves s i ghost)) = normalize 7 (Z.shiftr (to_Zpos (word_370 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_371. apply unsigned_slice. Qed.
Transparent word_380.
Lemma slice_shape_380 v : word_380 v = take 65 (drop 0 (word_379 v)).
Proof. unfold word_380, closed_380, expr_380, word_of_eval.
 rewrite drop0. reflexivity. Qed.
Opaque word_380.
Lemma slice_integer_380 s i ghost : to_Zpos (word_380 (encoded_leaves s i ghost)) = normalize 65 (Z.shiftr (to_Zpos (word_379 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_380. apply unsigned_slice. Qed.
Transparent word_382.
Lemma slice_shape_382 v : word_382 v = take 64 (drop 0 (word_381 v)).
Proof. unfold word_382, closed_382, expr_382, word_of_eval.
 change (drop 0 (take 64 (word_381 v)) = take 64 (drop 0 (word_381 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_382.
Lemma slice_integer_382 s i ghost : to_Zpos (word_382 (encoded_leaves s i ghost)) = normalize 64 (Z.shiftr (to_Zpos (word_381 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_382. apply unsigned_slice. Qed.
Transparent word_387.
Lemma slice_shape_387 v : word_387 v = take 6 (drop 0 (word_386 v)).
Proof. unfold word_387, closed_387, expr_387, word_of_eval.
 rewrite drop0. reflexivity. Qed.
Opaque word_387.
Lemma slice_integer_387 s i ghost : to_Zpos (word_387 (encoded_leaves s i ghost)) = normalize 6 (Z.shiftr (to_Zpos (word_386 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_387. apply unsigned_slice. Qed.
Transparent word_405.
Lemma slice_shape_405 v : word_405 v = take 64 (drop 1 (word_21 v)).
Proof. unfold word_405, closed_405, expr_405, word_of_eval.
 change (drop 1 (take 65 (word_21 v)) = take 64 (drop 1 (word_21 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_405.
Lemma slice_integer_405 s i ghost : to_Zpos (word_405 (encoded_leaves s i ghost)) = normalize 64 (Z.shiftr (to_Zpos (word_21 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_405. apply unsigned_slice. Qed.
Transparent word_407.
Lemma slice_shape_407 v : word_407 v = take 64 (drop 0 (word_406 v)).
Proof. unfold word_407, closed_407, expr_407, word_of_eval.
 rewrite drop0. reflexivity. Qed.
Opaque word_407.
Lemma slice_integer_407 s i ghost : to_Zpos (word_407 (encoded_leaves s i ghost)) = normalize 64 (Z.shiftr (to_Zpos (word_406 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_407. apply unsigned_slice. Qed.
Transparent word_410.
Lemma slice_shape_410 v : word_410 v = take 64 (drop 0 (word_409 v)).
Proof. unfold word_410, closed_410, expr_410, word_of_eval.
 rewrite drop0. reflexivity. Qed.
Opaque word_410.
Lemma slice_integer_410 s i ghost : to_Zpos (word_410 (encoded_leaves s i ghost)) = normalize 64 (Z.shiftr (to_Zpos (word_409 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_410. apply unsigned_slice. Qed.
Transparent word_413.
Lemma slice_shape_413 v : word_413 v = take 32 (drop 0 (word_412 v)).
Proof. unfold word_413, closed_413, expr_413, word_of_eval.
 change (drop 0 (take 32 (word_412 v)) = take 32 (drop 0 (word_412 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_413.
Lemma slice_integer_413 s i ghost : to_Zpos (word_413 (encoded_leaves s i ghost)) = normalize 32 (Z.shiftr (to_Zpos (word_412 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_413. apply unsigned_slice. Qed.
Transparent word_414.
Lemma slice_shape_414 v : word_414 v = take 1 (drop 31 (word_413 v)).
Proof. unfold word_414, closed_414, expr_414, word_of_eval.
 change (drop 31 (take 32 (word_413 v)) = take 1 (drop 31 (word_413 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_414.
Lemma slice_integer_414 s i ghost : to_Zpos (word_414 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_413 (encoded_leaves s i ghost))) 31).
Proof. rewrite slice_shape_414. apply unsigned_slice. Qed.
Transparent word_415.
Lemma slice_shape_415 v : word_415 v = take 1 (drop 0 (word_414 v)).
Proof. unfold word_415, closed_415, expr_415, word_of_eval.
 change (drop 0 (take 1 (word_414 v)) = take 1 (drop 0 (word_414 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_415.
Lemma slice_integer_415 s i ghost : to_Zpos (word_415 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_414 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_415. apply unsigned_slice. Qed.
Transparent word_422.
Lemma slice_shape_422 v : word_422 v = take 1 (drop 0 (word_1 v)).
Proof. unfold word_422, closed_422, expr_422, word_of_eval.
 change (drop 0 (take 1 (word_1 v)) = take 1 (drop 0 (word_1 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_422.
Lemma slice_integer_422 s i ghost : to_Zpos (word_422 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_1 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_422. apply unsigned_slice. Qed.
Transparent word_425.
Lemma slice_shape_425 v : word_425 v = take 64 (drop 1 (word_43 v)).
Proof. unfold word_425, closed_425, expr_425, word_of_eval.
 change (drop 1 (take 65 (word_43 v)) = take 64 (drop 1 (word_43 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_425.
Lemma slice_integer_425 s i ghost : to_Zpos (word_425 (encoded_leaves s i ghost)) = normalize 64 (Z.shiftr (to_Zpos (word_43 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_425. apply unsigned_slice. Qed.
Transparent word_427.
Lemma slice_shape_427 v : word_427 v = take 1 (drop 0 (word_1 v)).
Proof. unfold word_427, closed_427, expr_427, word_of_eval.
 change (drop 0 (take 1 (word_1 v)) = take 1 (drop 0 (word_1 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_427.
Lemma slice_integer_427 s i ghost : to_Zpos (word_427 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_1 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_427. apply unsigned_slice. Qed.
Transparent word_431.
Lemma slice_shape_431 v : word_431 v = take 1 (drop 0 (word_1 v)).
Proof. unfold word_431, closed_431, expr_431, word_of_eval.
 change (drop 0 (take 1 (word_1 v)) = take 1 (drop 0 (word_1 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_431.
Lemma slice_integer_431 s i ghost : to_Zpos (word_431 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_1 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_431. apply unsigned_slice. Qed.
Transparent word_436.
Lemma slice_shape_436 v : word_436 v = take 64 (drop 1 (word_43 v)).
Proof. unfold word_436, closed_436, expr_436, word_of_eval.
 change (drop 1 (take 65 (word_43 v)) = take 64 (drop 1 (word_43 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_436.
Lemma slice_integer_436 s i ghost : to_Zpos (word_436 (encoded_leaves s i ghost)) = normalize 64 (Z.shiftr (to_Zpos (word_43 (encoded_leaves s i ghost))) 1).
Proof. rewrite slice_shape_436. apply unsigned_slice. Qed.
Transparent word_438.
Lemma slice_shape_438 v : word_438 v = take 1 (drop 0 (word_1 v)).
Proof. unfold word_438, closed_438, expr_438, word_of_eval.
 change (drop 0 (take 1 (word_1 v)) = take 1 (drop 0 (word_1 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_438.
Lemma slice_integer_438 s i ghost : to_Zpos (word_438 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_1 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_438. apply unsigned_slice. Qed.
Transparent word_442.
Lemma slice_shape_442 v : word_442 v = take 1 (drop 0 (word_1 v)).
Proof. unfold word_442, closed_442, expr_442, word_of_eval.
 change (drop 0 (take 1 (word_1 v)) = take 1 (drop 0 (word_1 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_442.
Lemma slice_integer_442 s i ghost : to_Zpos (word_442 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_1 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_442. apply unsigned_slice. Qed.
Transparent word_450.
Lemma slice_shape_450 v : word_450 v = take 1 (drop 0 (word_1 v)).
Proof. unfold word_450, closed_450, expr_450, word_of_eval.
 change (drop 0 (take 1 (word_1 v)) = take 1 (drop 0 (word_1 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_450.
Lemma slice_integer_450 s i ghost : to_Zpos (word_450 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_1 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_450. apply unsigned_slice. Qed.
Transparent word_455.
Lemma slice_shape_455 v : word_455 v = take 1 (drop 0 (word_1 v)).
Proof. unfold word_455, closed_455, expr_455, word_of_eval.
 change (drop 0 (take 1 (word_1 v)) = take 1 (drop 0 (word_1 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_455.
Lemma slice_integer_455 s i ghost : to_Zpos (word_455 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_1 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_455. apply unsigned_slice. Qed.
Transparent word_462.
Lemma slice_shape_462 v : word_462 v = take 1 (drop 0 (word_1 v)).
Proof. unfold word_462, closed_462, expr_462, word_of_eval.
 change (drop 0 (take 1 (word_1 v)) = take 1 (drop 0 (word_1 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_462.
Lemma slice_integer_462 s i ghost : to_Zpos (word_462 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_1 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_462. apply unsigned_slice. Qed.
Transparent word_467.
Lemma slice_shape_467 v : word_467 v = take 6 (drop 0 (word_466 v)).
Proof. unfold word_467, closed_467, expr_467, word_of_eval.
 rewrite drop0. reflexivity. Qed.
Opaque word_467.
Lemma slice_integer_467 s i ghost : to_Zpos (word_467 (encoded_leaves s i ghost)) = normalize 6 (Z.shiftr (to_Zpos (word_466 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_467. apply unsigned_slice. Qed.
Transparent word_470.
Lemma slice_shape_470 v : word_470 v = take 1 (drop 0 (word_1 v)).
Proof. unfold word_470, closed_470, expr_470, word_of_eval.
 change (drop 0 (take 1 (word_1 v)) = take 1 (drop 0 (word_1 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_470.
Lemma slice_integer_470 s i ghost : to_Zpos (word_470 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_1 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_470. apply unsigned_slice. Qed.
Transparent word_477.
Lemma slice_shape_477 v : word_477 v = take 1 (drop 0 (word_1 v)).
Proof. unfold word_477, closed_477, expr_477, word_of_eval.
 change (drop 0 (take 1 (word_1 v)) = take 1 (drop 0 (word_1 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_477.
Lemma slice_integer_477 s i ghost : to_Zpos (word_477 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_1 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_477. apply unsigned_slice. Qed.
Transparent word_481.
Lemma slice_shape_481 v : word_481 v = take 1 (drop 0 (word_1 v)).
Proof. unfold word_481, closed_481, expr_481, word_of_eval.
 change (drop 0 (take 1 (word_1 v)) = take 1 (drop 0 (word_1 v))).
 rewrite slice_drop_take. reflexivity. Qed.
Opaque word_481.
Lemma slice_integer_481 s i ghost : to_Zpos (word_481 (encoded_leaves s i ghost)) = normalize 1 (Z.shiftr (to_Zpos (word_1 (encoded_leaves s i ghost))) 0).
Proof. rewrite slice_shape_481. apply unsigned_slice. Qed.
Print Assumptions slice_integer_481.
