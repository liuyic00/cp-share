From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From SmallMultiplier Require Import Stable.
Local Open Scope N_scope.

Lemma word_37_congr v w (H0 : word_3 v = word_3 w) : word_37 v = word_37 w.
Proof. unfold word_37, closed_word_37. rewrite H0. reflexivity. Qed.
Lemma word_37_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_37 v = word_37 w.
Proof. apply word_37_congr.
 - exact Hb.
Qed.
Lemma word_38_congr v w (H0 : word_3 v = word_3 w) (H1 : word_37 v = word_37 w) : word_38 v = word_38 w.
Proof. unfold word_38, closed_word_38. rewrite H0 H1. reflexivity. Qed.
Lemma word_38_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_38 v = word_38 w.
Proof. apply word_38_congr.
 - exact Hb.
 - apply word_37_inputs; assumption.
Qed.
Lemma word_39_congr v w (H0 : word_38 v = word_38 w) : word_39 v = word_39 w.
Proof. unfold word_39, closed_word_39. rewrite H0. reflexivity. Qed.
Lemma word_39_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_39 v = word_39 w.
Proof. apply word_39_congr.
 - apply word_38_inputs; assumption.
Qed.
Lemma word_40_congr v w (H0 : word_39 v = word_39 w) : word_40 v = word_40 w.
Proof. unfold word_40, closed_word_40. rewrite H0. reflexivity. Qed.
Lemma word_40_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_40 v = word_40 w.
Proof. apply word_40_congr.
 - apply word_39_inputs; assumption.
Qed.
Lemma word_41_congr v w (H0 : word_39 v = word_39 w) : word_41 v = word_41 w.
Proof. unfold word_41, closed_word_41. rewrite H0. reflexivity. Qed.
Lemma word_41_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_41 v = word_41 w.
Proof. apply word_41_congr.
 - apply word_39_inputs; assumption.
Qed.
Lemma word_42_congr v w (H0 : word_41 v = word_41 w) : word_42 v = word_42 w.
Proof. unfold word_42, closed_word_42. rewrite H0. reflexivity. Qed.
Lemma word_42_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_42 v = word_42 w.
Proof. apply word_42_congr.
 - apply word_41_inputs; assumption.
Qed.
Lemma word_43_congr v w (H0 : word_42 v = word_42 w) : word_43 v = word_43 w.
Proof. unfold word_43, closed_word_43. rewrite H0. reflexivity. Qed.
Lemma word_43_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_43 v = word_43 w.
Proof. apply word_43_congr.
 - apply word_42_inputs; assumption.
Qed.
Lemma word_44_congr v w (H0 : word_2 v = word_2 w) : word_44 v = word_44 w.
Proof. unfold word_44, closed_word_44. rewrite H0. reflexivity. Qed.
Lemma word_44_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_44 v = word_44 w.
Proof. apply word_44_congr.
 - exact Ha.
Qed.
Lemma word_45_congr v w (H0 : word_44 v = word_44 w) : word_45 v = word_45 w.
Proof. unfold word_45, closed_word_45. rewrite H0. reflexivity. Qed.
Lemma word_45_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_45 v = word_45 w.
Proof. apply word_45_congr.
 - apply word_44_inputs; assumption.
Qed.
Lemma word_46_congr v w (H0 : word_45 v = word_45 w) : word_46 v = word_46 w.
Proof. unfold word_46, closed_word_46. rewrite H0. reflexivity. Qed.
Lemma word_46_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_46 v = word_46 w.
Proof. apply word_46_congr.
 - apply word_45_inputs; assumption.
Qed.
Lemma word_47_congr v w (H0 : word_39 v = word_39 w) (H1 : word_46 v = word_46 w) : word_47 v = word_47 w.
Proof. unfold word_47, closed_word_47. rewrite H0 H1. reflexivity. Qed.
Lemma word_47_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_47 v = word_47 w.
Proof. apply word_47_congr.
 - apply word_39_inputs; assumption.
 - apply word_46_inputs; assumption.
Qed.
Lemma word_48_congr v w (H0 : word_45 v = word_45 w) : word_48 v = word_48 w.
Proof. unfold word_48, closed_word_48. rewrite H0. reflexivity. Qed.
Lemma word_48_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_48 v = word_48 w.
Proof. apply word_48_congr.
 - apply word_45_inputs; assumption.
Qed.
Lemma word_49_congr v w (H0 : word_39 v = word_39 w) (H1 : word_47 v = word_47 w) (H2 : word_48 v = word_48 w) : word_49 v = word_49 w.
Proof. unfold word_49, closed_word_49. rewrite H0 H1 H2. reflexivity. Qed.
Lemma word_49_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_49 v = word_49 w.
Proof. apply word_49_congr.
 - apply word_39_inputs; assumption.
 - apply word_47_inputs; assumption.
 - apply word_48_inputs; assumption.
Qed.
Lemma word_50_congr v w (H0 : word_45 v = word_45 w) : word_50 v = word_50 w.
Proof. unfold word_50, closed_word_50. rewrite H0. reflexivity. Qed.
Lemma word_50_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_50 v = word_50 w.
Proof. apply word_50_congr.
 - apply word_45_inputs; assumption.
Qed.
Lemma word_51_congr v w (H0 : word_40 v = word_40 w) : word_51 v = word_51 w.
Proof. unfold word_51, closed_word_51. rewrite H0. reflexivity. Qed.
Lemma word_51_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_51 v = word_51 w.
Proof. apply word_51_congr.
 - apply word_40_inputs; assumption.
Qed.
Lemma word_52_congr v w (H0 : word_49 v = word_49 w) (H1 : word_50 v = word_50 w) (H2 : word_51 v = word_51 w) : word_52 v = word_52 w.
Proof. unfold word_52, closed_word_52. rewrite H0 H1 H2. reflexivity. Qed.
Lemma word_52_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_52 v = word_52 w.
Proof. apply word_52_congr.
 - apply word_49_inputs; assumption.
 - apply word_50_inputs; assumption.
 - apply word_51_inputs; assumption.
Qed.
Lemma word_53_congr v w (H0 : word_45 v = word_45 w) : word_53 v = word_53 w.
Proof. unfold word_53, closed_word_53. rewrite H0. reflexivity. Qed.
Lemma word_53_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_53 v = word_53 w.
Proof. apply word_53_congr.
 - apply word_45_inputs; assumption.
Qed.
Lemma word_54_congr v w (H0 : word_43 v = word_43 w) : word_54 v = word_54 w.
Proof. unfold word_54, closed_word_54. rewrite H0. reflexivity. Qed.
Lemma word_54_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_54 v = word_54 w.
Proof. apply word_54_congr.
 - apply word_43_inputs; assumption.
Qed.
Lemma word_55_congr v w (H0 : word_52 v = word_52 w) (H1 : word_53 v = word_53 w) (H2 : word_54 v = word_54 w) : word_55 v = word_55 w.
Proof. unfold word_55, closed_word_55. rewrite H0 H1 H2. reflexivity. Qed.
Lemma word_55_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_55 v = word_55 w.
Proof. apply word_55_congr.
 - apply word_52_inputs; assumption.
 - apply word_53_inputs; assumption.
 - apply word_54_inputs; assumption.
Qed.
Lemma word_56_congr v w (H0 : word_45 v = word_45 w) : word_56 v = word_56 w.
Proof. unfold word_56, closed_word_56. rewrite H0. reflexivity. Qed.
Lemma word_56_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_56 v = word_56 w.
Proof. apply word_56_congr.
 - apply word_45_inputs; assumption.
Qed.
Lemma word_57_congr v w (H0 : word_42 v = word_42 w) (H1 : word_55 v = word_55 w) (H2 : word_56 v = word_56 w) : word_57 v = word_57 w.
Proof. unfold word_57, closed_word_57. rewrite H0 H1 H2. reflexivity. Qed.
Lemma word_57_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_57 v = word_57 w.
Proof. apply word_57_congr.
 - apply word_42_inputs; assumption.
 - apply word_55_inputs; assumption.
 - apply word_56_inputs; assumption.
Qed.
Lemma word_58_congr v w (H0 : word_45 v = word_45 w) : word_58 v = word_58 w.
Proof. unfold word_58, closed_word_58. rewrite H0. reflexivity. Qed.
Lemma word_58_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_58 v = word_58 w.
Proof. apply word_58_congr.
 - apply word_45_inputs; assumption.
Qed.
Lemma word_59_congr v w (H0 : word_42 v = word_42 w) (H1 : word_57 v = word_57 w) (H2 : word_58 v = word_58 w) : word_59 v = word_59 w.
Proof. unfold word_59, closed_word_59. rewrite H0 H1 H2. reflexivity. Qed.
Lemma word_59_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_59 v = word_59 w.
Proof. apply word_59_congr.
 - apply word_42_inputs; assumption.
 - apply word_57_inputs; assumption.
 - apply word_58_inputs; assumption.
Qed.
Lemma word_60_congr v w (H0 : word_59 v = word_59 w) : word_60 v = word_60 w.
Proof. unfold word_60, closed_word_60. rewrite H0. reflexivity. Qed.
Lemma word_60_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_60 v = word_60 w.
Proof. apply word_60_congr.
 - apply word_59_inputs; assumption.
Qed.
Lemma word_61_congr v w  : word_61 v = word_61 w.
Proof. unfold word_61, closed_word_61. reflexivity. Qed.
Lemma word_61_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_61 v = word_61 w.
Proof. apply word_61_congr.
Qed.
Lemma word_62_congr v w (H0 : word_61 v = word_61 w) : word_62 v = word_62 w.
Proof. unfold word_62, closed_word_62. rewrite H0. reflexivity. Qed.
Lemma word_62_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_62 v = word_62 w.
Proof. apply word_62_congr.
 - apply word_61_inputs; assumption.
Qed.
Lemma word_63_congr v w (H0 : word_62 v = word_62 w) : word_63 v = word_63 w.
Proof. unfold word_63, closed_word_63. rewrite H0. reflexivity. Qed.
Lemma word_63_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_63 v = word_63 w.
Proof. apply word_63_congr.
 - apply word_62_inputs; assumption.
Qed.
Lemma word_64_congr v w (H0 : word_61 v = word_61 w) : word_64 v = word_64 w.
Proof. unfold word_64, closed_word_64. rewrite H0. reflexivity. Qed.
Lemma word_64_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_64 v = word_64 w.
Proof. apply word_64_congr.
 - apply word_61_inputs; assumption.
Qed.
Lemma word_65_congr v w (H0 : word_63 v = word_63 w) (H1 : word_64 v = word_64 w) : word_65 v = word_65 w.
Proof. unfold word_65, closed_word_65. rewrite H0 H1. reflexivity. Qed.
Lemma word_65_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_65 v = word_65 w.
Proof. apply word_65_congr.
 - apply word_63_inputs; assumption.
 - apply word_64_inputs; assumption.
Qed.
Lemma word_66_congr v w (H0 : word_61 v = word_61 w) : word_66 v = word_66 w.
Proof. unfold word_66, closed_word_66. rewrite H0. reflexivity. Qed.
Lemma word_66_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_66 v = word_66 w.
Proof. apply word_66_congr.
 - apply word_61_inputs; assumption.
Qed.
Lemma word_67_congr v w (H0 : word_65 v = word_65 w) (H1 : word_66 v = word_66 w) : word_67 v = word_67 w.
Proof. unfold word_67, closed_word_67. rewrite H0 H1. reflexivity. Qed.
Lemma word_67_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_67 v = word_67 w.
Proof. apply word_67_congr.
 - apply word_65_inputs; assumption.
 - apply word_66_inputs; assumption.
Qed.
Lemma word_68_congr v w (H0 : word_60 v = word_60 w) : word_68 v = word_68 w.
Proof. unfold word_68, closed_word_68. rewrite H0. reflexivity. Qed.
Lemma word_68_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_68 v = word_68 w.
Proof. apply word_68_congr.
 - apply word_60_inputs; assumption.
Qed.
Lemma word_69_congr v w (H0 : word_59 v = word_59 w) (H1 : word_60 v = word_60 w) : word_69 v = word_69 w.
Proof. unfold word_69, closed_word_69. rewrite H0 H1. reflexivity. Qed.
Lemma word_69_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_69 v = word_69 w.
Proof. apply word_69_congr.
 - apply word_59_inputs; assumption.
 - apply word_60_inputs; assumption.
Qed.
Lemma word_70_congr v w (H0 : word_60 v = word_60 w) (H1 : word_68 v = word_68 w) : word_70 v = word_70 w.
Proof. unfold word_70, closed_word_70. rewrite H0 H1. reflexivity. Qed.
Lemma word_70_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_70 v = word_70 w.
Proof. apply word_70_congr.
 - apply word_60_inputs; assumption.
 - apply word_68_inputs; assumption.
Qed.
Lemma word_71_congr v w (H0 : word_69 v = word_69 w) (H1 : word_70 v = word_70 w) : word_71 v = word_71 w.
Proof. unfold word_71, closed_word_71. rewrite H0 H1. reflexivity. Qed.
Lemma word_71_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_71 v = word_71 w.
Proof. apply word_71_congr.
 - apply word_69_inputs; assumption.
 - apply word_70_inputs; assumption.
Qed.
Lemma word_72_congr v w (H0 : word_71 v = word_71 w) : word_72 v = word_72 w.
Proof. unfold word_72, closed_word_72. rewrite H0. reflexivity. Qed.
Lemma word_72_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_72 v = word_72 w.
Proof. apply word_72_congr.
 - apply word_71_inputs; assumption.
Qed.
Lemma word_73_congr v w (H0 : word_71 v = word_71 w) : word_73 v = word_73 w.
Proof. unfold word_73, closed_word_73. rewrite H0. reflexivity. Qed.
Lemma word_73_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_73 v = word_73 w.
Proof. apply word_73_congr.
 - apply word_71_inputs; assumption.
Qed.
Lemma word_74_congr v w (H0 : word_71 v = word_71 w) : word_74 v = word_74 w.
Proof. unfold word_74, closed_word_74. rewrite H0. reflexivity. Qed.
Lemma word_74_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_74 v = word_74 w.
Proof. apply word_74_congr.
 - apply word_71_inputs; assumption.
Qed.
Lemma word_75_congr v w (H0 : word_71 v = word_71 w) : word_75 v = word_75 w.
Proof. unfold word_75, closed_word_75. rewrite H0. reflexivity. Qed.
Lemma word_75_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_75 v = word_75 w.
Proof. apply word_75_congr.
 - apply word_71_inputs; assumption.
Qed.
Lemma word_76_congr v w (H0 : word_71 v = word_71 w) : word_76 v = word_76 w.
Proof. unfold word_76, closed_word_76. rewrite H0. reflexivity. Qed.
Lemma word_76_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_76 v = word_76 w.
Proof. apply word_76_congr.
 - apply word_71_inputs; assumption.
Qed.
Lemma word_77_congr v w (H0 : word_71 v = word_71 w) : word_77 v = word_77 w.
Proof. unfold word_77, closed_word_77. rewrite H0. reflexivity. Qed.
Lemma word_77_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_77 v = word_77 w.
Proof. apply word_77_congr.
 - apply word_71_inputs; assumption.
Qed.
Lemma word_78_congr v w (H0 : word_71 v = word_71 w) : word_78 v = word_78 w.
Proof. unfold word_78, closed_word_78. rewrite H0. reflexivity. Qed.
Lemma word_78_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_78 v = word_78 w.
Proof. apply word_78_congr.
 - apply word_71_inputs; assumption.
Qed.
Lemma word_79_congr v w (H0 : word_71 v = word_71 w) : word_79 v = word_79 w.
Proof. unfold word_79, closed_word_79. rewrite H0. reflexivity. Qed.
Lemma word_79_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_79 v = word_79 w.
Proof. apply word_79_congr.
 - apply word_71_inputs; assumption.
Qed.
Lemma word_80_congr v w (H0 : word_71 v = word_71 w) : word_80 v = word_80 w.
Proof. unfold word_80, closed_word_80. rewrite H0. reflexivity. Qed.
Lemma word_80_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_80 v = word_80 w.
Proof. apply word_80_congr.
 - apply word_71_inputs; assumption.
Qed.
Lemma word_81_congr v w (H0 : word_71 v = word_71 w) : word_81 v = word_81 w.
Proof. unfold word_81, closed_word_81. rewrite H0. reflexivity. Qed.
Lemma word_81_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_81 v = word_81 w.
Proof. apply word_81_congr.
 - apply word_71_inputs; assumption.
Qed.
Lemma word_82_congr v w (H0 : word_71 v = word_71 w) : word_82 v = word_82 w.
Proof. unfold word_82, closed_word_82. rewrite H0. reflexivity. Qed.
Lemma word_82_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_82 v = word_82 w.
Proof. apply word_82_congr.
 - apply word_71_inputs; assumption.
Qed.
Lemma word_83_congr v w (H0 : word_71 v = word_71 w) : word_83 v = word_83 w.
Proof. unfold word_83, closed_word_83. rewrite H0. reflexivity. Qed.
Lemma word_83_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_83 v = word_83 w.
Proof. apply word_83_congr.
 - apply word_71_inputs; assumption.
Qed.
Lemma word_84_congr v w (H0 : word_2 v = word_2 w) : word_84 v = word_84 w.
Proof. unfold word_84, closed_word_84. rewrite H0. reflexivity. Qed.
Lemma word_84_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_84 v = word_84 w.
Proof. apply word_84_congr.
 - exact Ha.
Qed.
Lemma word_85_congr v w (H0 : word_84 v = word_84 w) : word_85 v = word_85 w.
Proof. unfold word_85, closed_word_85. rewrite H0. reflexivity. Qed.
Lemma word_85_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_85 v = word_85 w.
Proof. apply word_85_congr.
 - apply word_84_inputs; assumption.
Qed.
Lemma word_86_congr v w (H0 : word_39 v = word_39 w) (H1 : word_85 v = word_85 w) : word_86 v = word_86 w.
Proof. unfold word_86, closed_word_86. rewrite H0 H1. reflexivity. Qed.
Lemma word_86_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_86 v = word_86 w.
Proof. apply word_86_congr.
 - apply word_39_inputs; assumption.
 - apply word_85_inputs; assumption.
Qed.
Lemma word_87_congr v w (H0 : word_84 v = word_84 w) : word_87 v = word_87 w.
Proof. unfold word_87, closed_word_87. rewrite H0. reflexivity. Qed.
Lemma word_87_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_87 v = word_87 w.
Proof. apply word_87_congr.
 - apply word_84_inputs; assumption.
Qed.
Lemma word_88_congr v w (H0 : word_39 v = word_39 w) (H1 : word_86 v = word_86 w) (H2 : word_87 v = word_87 w) : word_88 v = word_88 w.
Proof. unfold word_88, closed_word_88. rewrite H0 H1 H2. reflexivity. Qed.
Lemma word_88_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_88 v = word_88 w.
Proof. apply word_88_congr.
 - apply word_39_inputs; assumption.
 - apply word_86_inputs; assumption.
 - apply word_87_inputs; assumption.
Qed.
Lemma word_89_congr v w (H0 : word_84 v = word_84 w) : word_89 v = word_89 w.
Proof. unfold word_89, closed_word_89. rewrite H0. reflexivity. Qed.
Lemma word_89_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_89 v = word_89 w.
Proof. apply word_89_congr.
 - apply word_84_inputs; assumption.
Qed.
Lemma word_90_congr v w (H0 : word_51 v = word_51 w) (H1 : word_88 v = word_88 w) (H2 : word_89 v = word_89 w) : word_90 v = word_90 w.
Proof. unfold word_90, closed_word_90. rewrite H0 H1 H2. reflexivity. Qed.
Lemma word_90_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_90 v = word_90 w.
Proof. apply word_90_congr.
 - apply word_51_inputs; assumption.
 - apply word_88_inputs; assumption.
 - apply word_89_inputs; assumption.
Qed.
Lemma word_91_congr v w (H0 : word_84 v = word_84 w) : word_91 v = word_91 w.
Proof. unfold word_91, closed_word_91. rewrite H0. reflexivity. Qed.
Lemma word_91_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_91 v = word_91 w.
Proof. apply word_91_congr.
 - apply word_84_inputs; assumption.
Qed.
Lemma word_92_congr v w (H0 : word_54 v = word_54 w) (H1 : word_90 v = word_90 w) (H2 : word_91 v = word_91 w) : word_92 v = word_92 w.
Proof. unfold word_92, closed_word_92. rewrite H0 H1 H2. reflexivity. Qed.
Lemma word_92_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_92 v = word_92 w.
Proof. apply word_92_congr.
 - apply word_54_inputs; assumption.
 - apply word_90_inputs; assumption.
 - apply word_91_inputs; assumption.
Qed.
Lemma word_93_congr v w (H0 : word_84 v = word_84 w) : word_93 v = word_93 w.
Proof. unfold word_93, closed_word_93. rewrite H0. reflexivity. Qed.
Lemma word_93_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_93 v = word_93 w.
Proof. apply word_93_congr.
 - apply word_84_inputs; assumption.
Qed.
Lemma word_94_congr v w (H0 : word_42 v = word_42 w) (H1 : word_92 v = word_92 w) (H2 : word_93 v = word_93 w) : word_94 v = word_94 w.
Proof. unfold word_94, closed_word_94. rewrite H0 H1 H2. reflexivity. Qed.
Lemma word_94_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_94 v = word_94 w.
Proof. apply word_94_congr.
 - apply word_42_inputs; assumption.
 - apply word_92_inputs; assumption.
 - apply word_93_inputs; assumption.
Qed.
Lemma word_95_congr v w (H0 : word_84 v = word_84 w) : word_95 v = word_95 w.
Proof. unfold word_95, closed_word_95. rewrite H0. reflexivity. Qed.
Lemma word_95_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_95 v = word_95 w.
Proof. apply word_95_congr.
 - apply word_84_inputs; assumption.
Qed.
Lemma word_96_congr v w (H0 : word_42 v = word_42 w) (H1 : word_94 v = word_94 w) (H2 : word_95 v = word_95 w) : word_96 v = word_96 w.
Proof. unfold word_96, closed_word_96. rewrite H0 H1 H2. reflexivity. Qed.
Lemma word_96_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_96 v = word_96 w.
Proof. apply word_96_congr.
 - apply word_42_inputs; assumption.
 - apply word_94_inputs; assumption.
 - apply word_95_inputs; assumption.
Qed.
Lemma word_97_congr v w (H0 : word_96 v = word_96 w) : word_97 v = word_97 w.
Proof. unfold word_97, closed_word_97. rewrite H0. reflexivity. Qed.
Lemma word_97_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_97 v = word_97 w.
Proof. apply word_97_congr.
 - apply word_96_inputs; assumption.
Qed.
Lemma word_98_congr v w (H0 : word_45 v = word_45 w) : word_98 v = word_98 w.
Proof. unfold word_98, closed_word_98. rewrite H0. reflexivity. Qed.
Lemma word_98_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_98 v = word_98 w.
Proof. apply word_98_congr.
 - apply word_45_inputs; assumption.
Qed.
Lemma word_99_congr v w (H0 : word_98 v = word_98 w) : word_99 v = word_99 w.
Proof. unfold word_99, closed_word_99. rewrite H0. reflexivity. Qed.
Lemma word_99_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_99 v = word_99 w.
Proof. apply word_99_congr.
 - apply word_98_inputs; assumption.
Qed.
Lemma word_100_congr v w (H0 : word_45 v = word_45 w) : word_100 v = word_100 w.
Proof. unfold word_100, closed_word_100. rewrite H0. reflexivity. Qed.
Lemma word_100_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_100 v = word_100 w.
Proof. apply word_100_congr.
 - apply word_45_inputs; assumption.
Qed.
Lemma word_101_congr v w (H0 : word_99 v = word_99 w) (H1 : word_100 v = word_100 w) : word_101 v = word_101 w.
Proof. unfold word_101, closed_word_101. rewrite H0 H1. reflexivity. Qed.
Lemma word_101_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_101 v = word_101 w.
Proof. apply word_101_congr.
 - apply word_99_inputs; assumption.
 - apply word_100_inputs; assumption.
Qed.
Lemma word_102_congr v w (H0 : word_45 v = word_45 w) : word_102 v = word_102 w.
Proof. unfold word_102, closed_word_102. rewrite H0. reflexivity. Qed.
Lemma word_102_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_102 v = word_102 w.
Proof. apply word_102_congr.
 - apply word_45_inputs; assumption.
Qed.
Lemma word_103_congr v w (H0 : word_101 v = word_101 w) (H1 : word_102 v = word_102 w) : word_103 v = word_103 w.
Proof. unfold word_103, closed_word_103. rewrite H0 H1. reflexivity. Qed.
Lemma word_103_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_103 v = word_103 w.
Proof. apply word_103_congr.
 - apply word_101_inputs; assumption.
 - apply word_102_inputs; assumption.
Qed.
Lemma word_104_congr v w (H0 : word_97 v = word_97 w) : word_104 v = word_104 w.
Proof. unfold word_104, closed_word_104. rewrite H0. reflexivity. Qed.
Lemma word_104_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_104 v = word_104 w.
Proof. apply word_104_congr.
 - apply word_97_inputs; assumption.
Qed.
Lemma word_105_congr v w (H0 : word_96 v = word_96 w) (H1 : word_103 v = word_103 w) : word_105 v = word_105 w.
Proof. unfold word_105, closed_word_105. rewrite H0 H1. reflexivity. Qed.
Lemma word_105_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_105 v = word_105 w.
Proof. apply word_105_congr.
 - apply word_96_inputs; assumption.
 - apply word_103_inputs; assumption.
Qed.
Lemma word_106_congr v w (H0 : word_104 v = word_104 w) : word_106 v = word_106 w.
Proof. unfold word_106, closed_word_106. rewrite H0. reflexivity. Qed.
Lemma word_106_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_106 v = word_106 w.
Proof. apply word_106_congr.
 - apply word_104_inputs; assumption.
Qed.
Lemma word_107_congr v w (H0 : word_105 v = word_105 w) (H1 : word_106 v = word_106 w) : word_107 v = word_107 w.
Proof. unfold word_107, closed_word_107. rewrite H0 H1. reflexivity. Qed.
Lemma word_107_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_107 v = word_107 w.
Proof. apply word_107_congr.
 - apply word_105_inputs; assumption.
 - apply word_106_inputs; assumption.
Qed.
Lemma word_108_congr v w (H0 : word_107 v = word_107 w) : word_108 v = word_108 w.
Proof. unfold word_108, closed_word_108. rewrite H0. reflexivity. Qed.
Lemma word_108_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_108 v = word_108 w.
Proof. apply word_108_congr.
 - apply word_107_inputs; assumption.
Qed.
Lemma word_109_congr v w (H0 : word_107 v = word_107 w) : word_109 v = word_109 w.
Proof. unfold word_109, closed_word_109. rewrite H0. reflexivity. Qed.
Lemma word_109_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_109 v = word_109 w.
Proof. apply word_109_congr.
 - apply word_107_inputs; assumption.
Qed.
Lemma word_110_congr v w (H0 : word_107 v = word_107 w) : word_110 v = word_110 w.
Proof. unfold word_110, closed_word_110. rewrite H0. reflexivity. Qed.
Lemma word_110_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_110 v = word_110 w.
Proof. apply word_110_congr.
 - apply word_107_inputs; assumption.
Qed.
Lemma word_111_congr v w (H0 : word_107 v = word_107 w) : word_111 v = word_111 w.
Proof. unfold word_111, closed_word_111. rewrite H0. reflexivity. Qed.
Lemma word_111_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_111 v = word_111 w.
Proof. apply word_111_congr.
 - apply word_107_inputs; assumption.
Qed.
Lemma word_112_congr v w (H0 : word_107 v = word_107 w) : word_112 v = word_112 w.
Proof. unfold word_112, closed_word_112. rewrite H0. reflexivity. Qed.
Lemma word_112_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_112 v = word_112 w.
Proof. apply word_112_congr.
 - apply word_107_inputs; assumption.
Qed.
Lemma word_113_congr v w (H0 : word_107 v = word_107 w) : word_113 v = word_113 w.
Proof. unfold word_113, closed_word_113. rewrite H0. reflexivity. Qed.
Lemma word_113_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_113 v = word_113 w.
Proof. apply word_113_congr.
 - apply word_107_inputs; assumption.
Qed.
Lemma word_114_congr v w (H0 : word_107 v = word_107 w) : word_114 v = word_114 w.
Proof. unfold word_114, closed_word_114. rewrite H0. reflexivity. Qed.
Lemma word_114_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_114 v = word_114 w.
Proof. apply word_114_congr.
 - apply word_107_inputs; assumption.
Qed.
Lemma word_115_congr v w (H0 : word_107 v = word_107 w) : word_115 v = word_115 w.
Proof. unfold word_115, closed_word_115. rewrite H0. reflexivity. Qed.
Lemma word_115_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_115 v = word_115 w.
Proof. apply word_115_congr.
 - apply word_107_inputs; assumption.
Qed.
Lemma word_116_congr v w (H0 : word_107 v = word_107 w) : word_116 v = word_116 w.
Proof. unfold word_116, closed_word_116. rewrite H0. reflexivity. Qed.
Lemma word_116_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_116 v = word_116 w.
Proof. apply word_116_congr.
 - apply word_107_inputs; assumption.
Qed.
Lemma word_117_congr v w (H0 : word_107 v = word_107 w) : word_117 v = word_117 w.
Proof. unfold word_117, closed_word_117. rewrite H0. reflexivity. Qed.
Lemma word_117_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_117 v = word_117 w.
Proof. apply word_117_congr.
 - apply word_107_inputs; assumption.
Qed.
Lemma word_118_congr v w (H0 : word_107 v = word_107 w) : word_118 v = word_118 w.
Proof. unfold word_118, closed_word_118. rewrite H0. reflexivity. Qed.
Lemma word_118_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_118 v = word_118 w.
Proof. apply word_118_congr.
 - apply word_107_inputs; assumption.
Qed.
Lemma word_119_congr v w (H0 : word_107 v = word_107 w) : word_119 v = word_119 w.
Proof. unfold word_119, closed_word_119. rewrite H0. reflexivity. Qed.
Lemma word_119_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_119 v = word_119 w.
Proof. apply word_119_congr.
 - apply word_107_inputs; assumption.
Qed.
Lemma word_120_congr v w (H0 : word_107 v = word_107 w) : word_120 v = word_120 w.
Proof. unfold word_120, closed_word_120. rewrite H0. reflexivity. Qed.
Lemma word_120_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_120 v = word_120 w.
Proof. apply word_120_congr.
 - apply word_107_inputs; assumption.
Qed.
Lemma word_121_congr v w (H0 : word_2 v = word_2 w) : word_121 v = word_121 w.
Proof. unfold word_121, closed_word_121. rewrite H0. reflexivity. Qed.
Lemma word_121_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_121 v = word_121 w.
Proof. apply word_121_congr.
 - exact Ha.
Qed.
Lemma word_122_congr v w (H0 : word_121 v = word_121 w) : word_122 v = word_122 w.
Proof. unfold word_122, closed_word_122. rewrite H0. reflexivity. Qed.
Lemma word_122_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_122 v = word_122 w.
Proof. apply word_122_congr.
 - apply word_121_inputs; assumption.
Qed.
Lemma word_123_congr v w (H0 : word_39 v = word_39 w) (H1 : word_122 v = word_122 w) : word_123 v = word_123 w.
Proof. unfold word_123, closed_word_123. rewrite H0 H1. reflexivity. Qed.
Lemma word_123_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_123 v = word_123 w.
Proof. apply word_123_congr.
 - apply word_39_inputs; assumption.
 - apply word_122_inputs; assumption.
Qed.
Lemma word_124_congr v w (H0 : word_121 v = word_121 w) : word_124 v = word_124 w.
Proof. unfold word_124, closed_word_124. rewrite H0. reflexivity. Qed.
Lemma word_124_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_124 v = word_124 w.
Proof. apply word_124_congr.
 - apply word_121_inputs; assumption.
Qed.
Lemma word_125_congr v w (H0 : word_39 v = word_39 w) (H1 : word_123 v = word_123 w) (H2 : word_124 v = word_124 w) : word_125 v = word_125 w.
Proof. unfold word_125, closed_word_125. rewrite H0 H1 H2. reflexivity. Qed.
Lemma word_125_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_125 v = word_125 w.
Proof. apply word_125_congr.
 - apply word_39_inputs; assumption.
 - apply word_123_inputs; assumption.
 - apply word_124_inputs; assumption.
Qed.
Lemma word_126_congr v w (H0 : word_121 v = word_121 w) : word_126 v = word_126 w.
Proof. unfold word_126, closed_word_126. rewrite H0. reflexivity. Qed.
Lemma word_126_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_126 v = word_126 w.
Proof. apply word_126_congr.
 - apply word_121_inputs; assumption.
Qed.
Lemma word_127_congr v w (H0 : word_51 v = word_51 w) (H1 : word_125 v = word_125 w) (H2 : word_126 v = word_126 w) : word_127 v = word_127 w.
Proof. unfold word_127, closed_word_127. rewrite H0 H1 H2. reflexivity. Qed.
Lemma word_127_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_127 v = word_127 w.
Proof. apply word_127_congr.
 - apply word_51_inputs; assumption.
 - apply word_125_inputs; assumption.
 - apply word_126_inputs; assumption.
Qed.
Lemma word_128_congr v w (H0 : word_121 v = word_121 w) : word_128 v = word_128 w.
Proof. unfold word_128, closed_word_128. rewrite H0. reflexivity. Qed.
Lemma word_128_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_128 v = word_128 w.
Proof. apply word_128_congr.
 - apply word_121_inputs; assumption.
Qed.
Lemma word_129_congr v w (H0 : word_54 v = word_54 w) (H1 : word_127 v = word_127 w) (H2 : word_128 v = word_128 w) : word_129 v = word_129 w.
Proof. unfold word_129, closed_word_129. rewrite H0 H1 H2. reflexivity. Qed.
Lemma word_129_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_129 v = word_129 w.
Proof. apply word_129_congr.
 - apply word_54_inputs; assumption.
 - apply word_127_inputs; assumption.
 - apply word_128_inputs; assumption.
Qed.
Lemma word_130_congr v w (H0 : word_121 v = word_121 w) : word_130 v = word_130 w.
Proof. unfold word_130, closed_word_130. rewrite H0. reflexivity. Qed.
Lemma word_130_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_130 v = word_130 w.
Proof. apply word_130_congr.
 - apply word_121_inputs; assumption.
Qed.
Lemma word_131_congr v w (H0 : word_42 v = word_42 w) (H1 : word_129 v = word_129 w) (H2 : word_130 v = word_130 w) : word_131 v = word_131 w.
Proof. unfold word_131, closed_word_131. rewrite H0 H1 H2. reflexivity. Qed.
Lemma word_131_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_131 v = word_131 w.
Proof. apply word_131_congr.
 - apply word_42_inputs; assumption.
 - apply word_129_inputs; assumption.
 - apply word_130_inputs; assumption.
Qed.
Lemma word_132_congr v w (H0 : word_121 v = word_121 w) : word_132 v = word_132 w.
Proof. unfold word_132, closed_word_132. rewrite H0. reflexivity. Qed.
Lemma word_132_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_132 v = word_132 w.
Proof. apply word_132_congr.
 - apply word_121_inputs; assumption.
Qed.
Lemma word_133_congr v w (H0 : word_42 v = word_42 w) (H1 : word_131 v = word_131 w) (H2 : word_132 v = word_132 w) : word_133 v = word_133 w.
Proof. unfold word_133, closed_word_133. rewrite H0 H1 H2. reflexivity. Qed.
Lemma word_133_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_133 v = word_133 w.
Proof. apply word_133_congr.
 - apply word_42_inputs; assumption.
 - apply word_131_inputs; assumption.
 - apply word_132_inputs; assumption.
Qed.
Lemma word_134_congr v w (H0 : word_133 v = word_133 w) : word_134 v = word_134 w.
Proof. unfold word_134, closed_word_134. rewrite H0. reflexivity. Qed.
Lemma word_134_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_134 v = word_134 w.
Proof. apply word_134_congr.
 - apply word_133_inputs; assumption.
Qed.
Lemma word_135_congr v w (H0 : word_84 v = word_84 w) : word_135 v = word_135 w.
Proof. unfold word_135, closed_word_135. rewrite H0. reflexivity. Qed.
Lemma word_135_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_135 v = word_135 w.
Proof. apply word_135_congr.
 - apply word_84_inputs; assumption.
Qed.
Lemma word_136_congr v w (H0 : word_135 v = word_135 w) : word_136 v = word_136 w.
Proof. unfold word_136, closed_word_136. rewrite H0. reflexivity. Qed.
Lemma word_136_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_136 v = word_136 w.
Proof. apply word_136_congr.
 - apply word_135_inputs; assumption.
Qed.
Lemma word_137_congr v w (H0 : word_84 v = word_84 w) : word_137 v = word_137 w.
Proof. unfold word_137, closed_word_137. rewrite H0. reflexivity. Qed.
Lemma word_137_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_137 v = word_137 w.
Proof. apply word_137_congr.
 - apply word_84_inputs; assumption.
Qed.
Lemma word_138_congr v w (H0 : word_136 v = word_136 w) (H1 : word_137 v = word_137 w) : word_138 v = word_138 w.
Proof. unfold word_138, closed_word_138. rewrite H0 H1. reflexivity. Qed.
Lemma word_138_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_138 v = word_138 w.
Proof. apply word_138_congr.
 - apply word_136_inputs; assumption.
 - apply word_137_inputs; assumption.
Qed.
Lemma word_139_congr v w (H0 : word_84 v = word_84 w) : word_139 v = word_139 w.
Proof. unfold word_139, closed_word_139. rewrite H0. reflexivity. Qed.
Lemma word_139_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_139 v = word_139 w.
Proof. apply word_139_congr.
 - apply word_84_inputs; assumption.
Qed.
Lemma word_140_congr v w (H0 : word_138 v = word_138 w) (H1 : word_139 v = word_139 w) : word_140 v = word_140 w.
Proof. unfold word_140, closed_word_140. rewrite H0 H1. reflexivity. Qed.
Lemma word_140_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_140 v = word_140 w.
Proof. apply word_140_congr.
 - apply word_138_inputs; assumption.
 - apply word_139_inputs; assumption.
Qed.
Lemma word_141_congr v w (H0 : word_134 v = word_134 w) : word_141 v = word_141 w.
Proof. unfold word_141, closed_word_141. rewrite H0. reflexivity. Qed.
Lemma word_141_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_141 v = word_141 w.
Proof. apply word_141_congr.
 - apply word_134_inputs; assumption.
Qed.
Lemma word_142_congr v w (H0 : word_133 v = word_133 w) (H1 : word_140 v = word_140 w) : word_142 v = word_142 w.
Proof. unfold word_142, closed_word_142. rewrite H0 H1. reflexivity. Qed.
Lemma word_142_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_142 v = word_142 w.
Proof. apply word_142_congr.
 - apply word_133_inputs; assumption.
 - apply word_140_inputs; assumption.
Qed.
Lemma word_143_congr v w (H0 : word_141 v = word_141 w) : word_143 v = word_143 w.
Proof. unfold word_143, closed_word_143. rewrite H0. reflexivity. Qed.
Lemma word_143_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_143 v = word_143 w.
Proof. apply word_143_congr.
 - apply word_141_inputs; assumption.
Qed.
Lemma word_144_congr v w (H0 : word_142 v = word_142 w) (H1 : word_143 v = word_143 w) : word_144 v = word_144 w.
Proof. unfold word_144, closed_word_144. rewrite H0 H1. reflexivity. Qed.
Lemma word_144_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_144 v = word_144 w.
Proof. apply word_144_congr.
 - apply word_142_inputs; assumption.
 - apply word_143_inputs; assumption.
Qed.
Lemma word_145_congr v w (H0 : word_144 v = word_144 w) : word_145 v = word_145 w.
Proof. unfold word_145, closed_word_145. rewrite H0. reflexivity. Qed.
Lemma word_145_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_145 v = word_145 w.
Proof. apply word_145_congr.
 - apply word_144_inputs; assumption.
Qed.
Lemma word_146_congr v w (H0 : word_144 v = word_144 w) : word_146 v = word_146 w.
Proof. unfold word_146, closed_word_146. rewrite H0. reflexivity. Qed.
Lemma word_146_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_146 v = word_146 w.
Proof. apply word_146_congr.
 - apply word_144_inputs; assumption.
Qed.
Lemma word_147_congr v w (H0 : word_144 v = word_144 w) : word_147 v = word_147 w.
Proof. unfold word_147, closed_word_147. rewrite H0. reflexivity. Qed.
Lemma word_147_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_147 v = word_147 w.
Proof. apply word_147_congr.
 - apply word_144_inputs; assumption.
Qed.
Lemma word_148_congr v w (H0 : word_144 v = word_144 w) : word_148 v = word_148 w.
Proof. unfold word_148, closed_word_148. rewrite H0. reflexivity. Qed.
Lemma word_148_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_148 v = word_148 w.
Proof. apply word_148_congr.
 - apply word_144_inputs; assumption.
Qed.
Lemma word_149_congr v w (H0 : word_144 v = word_144 w) : word_149 v = word_149 w.
Proof. unfold word_149, closed_word_149. rewrite H0. reflexivity. Qed.
Lemma word_149_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_149 v = word_149 w.
Proof. apply word_149_congr.
 - apply word_144_inputs; assumption.
Qed.
Lemma word_150_congr v w (H0 : word_144 v = word_144 w) : word_150 v = word_150 w.
Proof. unfold word_150, closed_word_150. rewrite H0. reflexivity. Qed.
Lemma word_150_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_150 v = word_150 w.
Proof. apply word_150_congr.
 - apply word_144_inputs; assumption.
Qed.
Lemma word_151_congr v w (H0 : word_144 v = word_144 w) : word_151 v = word_151 w.
Proof. unfold word_151, closed_word_151. rewrite H0. reflexivity. Qed.
Lemma word_151_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_151 v = word_151 w.
Proof. apply word_151_congr.
 - apply word_144_inputs; assumption.
Qed.
Lemma word_152_congr v w (H0 : word_144 v = word_144 w) : word_152 v = word_152 w.
Proof. unfold word_152, closed_word_152. rewrite H0. reflexivity. Qed.
Lemma word_152_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_152 v = word_152 w.
Proof. apply word_152_congr.
 - apply word_144_inputs; assumption.
Qed.
Lemma word_153_congr v w (H0 : word_144 v = word_144 w) : word_153 v = word_153 w.
Proof. unfold word_153, closed_word_153. rewrite H0. reflexivity. Qed.
Lemma word_153_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_153 v = word_153 w.
Proof. apply word_153_congr.
 - apply word_144_inputs; assumption.
Qed.
Lemma word_154_congr v w (H0 : word_144 v = word_144 w) : word_154 v = word_154 w.
Proof. unfold word_154, closed_word_154. rewrite H0. reflexivity. Qed.
Lemma word_154_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_154 v = word_154 w.
Proof. apply word_154_congr.
 - apply word_144_inputs; assumption.
Qed.
Lemma word_155_congr v w (H0 : word_144 v = word_144 w) : word_155 v = word_155 w.
Proof. unfold word_155, closed_word_155. rewrite H0. reflexivity. Qed.
Lemma word_155_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_155 v = word_155 w.
Proof. apply word_155_congr.
 - apply word_144_inputs; assumption.
Qed.
Lemma word_156_congr v w (H0 : word_144 v = word_144 w) : word_156 v = word_156 w.
Proof. unfold word_156, closed_word_156. rewrite H0. reflexivity. Qed.
Lemma word_156_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_156 v = word_156 w.
Proof. apply word_156_congr.
 - apply word_144_inputs; assumption.
Qed.
Lemma word_157_congr v w (H0 : word_144 v = word_144 w) : word_157 v = word_157 w.
Proof. unfold word_157, closed_word_157. rewrite H0. reflexivity. Qed.
Lemma word_157_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_157 v = word_157 w.
Proof. apply word_157_congr.
 - apply word_144_inputs; assumption.
Qed.
Lemma word_158_congr v w (H0 : word_2 v = word_2 w) : word_158 v = word_158 w.
Proof. unfold word_158, closed_word_158. rewrite H0. reflexivity. Qed.
Lemma word_158_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_158 v = word_158 w.
Proof. apply word_158_congr.
 - exact Ha.
Qed.
Lemma word_159_congr v w (H0 : word_158 v = word_158 w) : word_159 v = word_159 w.
Proof. unfold word_159, closed_word_159. rewrite H0. reflexivity. Qed.
Lemma word_159_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_159 v = word_159 w.
Proof. apply word_159_congr.
 - apply word_158_inputs; assumption.
Qed.
Lemma word_160_congr v w (H0 : word_39 v = word_39 w) (H1 : word_159 v = word_159 w) : word_160 v = word_160 w.
Proof. unfold word_160, closed_word_160. rewrite H0 H1. reflexivity. Qed.
Lemma word_160_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_160 v = word_160 w.
Proof. apply word_160_congr.
 - apply word_39_inputs; assumption.
 - apply word_159_inputs; assumption.
Qed.
Lemma word_161_congr v w (H0 : word_158 v = word_158 w) : word_161 v = word_161 w.
Proof. unfold word_161, closed_word_161. rewrite H0. reflexivity. Qed.
Lemma word_161_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_161 v = word_161 w.
Proof. apply word_161_congr.
 - apply word_158_inputs; assumption.
Qed.
Lemma word_162_congr v w (H0 : word_39 v = word_39 w) (H1 : word_160 v = word_160 w) (H2 : word_161 v = word_161 w) : word_162 v = word_162 w.
Proof. unfold word_162, closed_word_162. rewrite H0 H1 H2. reflexivity. Qed.
Lemma word_162_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_162 v = word_162 w.
Proof. apply word_162_congr.
 - apply word_39_inputs; assumption.
 - apply word_160_inputs; assumption.
 - apply word_161_inputs; assumption.
Qed.
Lemma word_163_congr v w (H0 : word_158 v = word_158 w) : word_163 v = word_163 w.
Proof. unfold word_163, closed_word_163. rewrite H0. reflexivity. Qed.
Lemma word_163_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_163 v = word_163 w.
Proof. apply word_163_congr.
 - apply word_158_inputs; assumption.
Qed.
Lemma word_164_congr v w (H0 : word_51 v = word_51 w) (H1 : word_162 v = word_162 w) (H2 : word_163 v = word_163 w) : word_164 v = word_164 w.
Proof. unfold word_164, closed_word_164. rewrite H0 H1 H2. reflexivity. Qed.
Lemma word_164_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_164 v = word_164 w.
Proof. apply word_164_congr.
 - apply word_51_inputs; assumption.
 - apply word_162_inputs; assumption.
 - apply word_163_inputs; assumption.
Qed.
Lemma word_165_congr v w (H0 : word_158 v = word_158 w) : word_165 v = word_165 w.
Proof. unfold word_165, closed_word_165. rewrite H0. reflexivity. Qed.
Lemma word_165_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_165 v = word_165 w.
Proof. apply word_165_congr.
 - apply word_158_inputs; assumption.
Qed.
Lemma word_166_congr v w (H0 : word_54 v = word_54 w) (H1 : word_164 v = word_164 w) (H2 : word_165 v = word_165 w) : word_166 v = word_166 w.
Proof. unfold word_166, closed_word_166. rewrite H0 H1 H2. reflexivity. Qed.
Lemma word_166_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_166 v = word_166 w.
Proof. apply word_166_congr.
 - apply word_54_inputs; assumption.
 - apply word_164_inputs; assumption.
 - apply word_165_inputs; assumption.
Qed.
Lemma word_167_congr v w (H0 : word_158 v = word_158 w) : word_167 v = word_167 w.
Proof. unfold word_167, closed_word_167. rewrite H0. reflexivity. Qed.
Lemma word_167_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_167 v = word_167 w.
Proof. apply word_167_congr.
 - apply word_158_inputs; assumption.
Qed.
Lemma word_168_congr v w (H0 : word_42 v = word_42 w) (H1 : word_166 v = word_166 w) (H2 : word_167 v = word_167 w) : word_168 v = word_168 w.
Proof. unfold word_168, closed_word_168. rewrite H0 H1 H2. reflexivity. Qed.
Lemma word_168_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_168 v = word_168 w.
Proof. apply word_168_congr.
 - apply word_42_inputs; assumption.
 - apply word_166_inputs; assumption.
 - apply word_167_inputs; assumption.
Qed.
Lemma word_169_congr v w (H0 : word_158 v = word_158 w) : word_169 v = word_169 w.
Proof. unfold word_169, closed_word_169. rewrite H0. reflexivity. Qed.
Lemma word_169_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_169 v = word_169 w.
Proof. apply word_169_congr.
 - apply word_158_inputs; assumption.
Qed.
Lemma word_170_congr v w (H0 : word_42 v = word_42 w) (H1 : word_168 v = word_168 w) (H2 : word_169 v = word_169 w) : word_170 v = word_170 w.
Proof. unfold word_170, closed_word_170. rewrite H0 H1 H2. reflexivity. Qed.
Lemma word_170_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_170 v = word_170 w.
Proof. apply word_170_congr.
 - apply word_42_inputs; assumption.
 - apply word_168_inputs; assumption.
 - apply word_169_inputs; assumption.
Qed.
Lemma word_171_congr v w (H0 : word_170 v = word_170 w) : word_171 v = word_171 w.
Proof. unfold word_171, closed_word_171. rewrite H0. reflexivity. Qed.
Lemma word_171_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_171 v = word_171 w.
Proof. apply word_171_congr.
 - apply word_170_inputs; assumption.
Qed.
Lemma word_172_congr v w (H0 : word_121 v = word_121 w) : word_172 v = word_172 w.
Proof. unfold word_172, closed_word_172. rewrite H0. reflexivity. Qed.
Lemma word_172_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_172 v = word_172 w.
Proof. apply word_172_congr.
 - apply word_121_inputs; assumption.
Qed.
Lemma word_173_congr v w (H0 : word_172 v = word_172 w) : word_173 v = word_173 w.
Proof. unfold word_173, closed_word_173. rewrite H0. reflexivity. Qed.
Lemma word_173_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_173 v = word_173 w.
Proof. apply word_173_congr.
 - apply word_172_inputs; assumption.
Qed.
Lemma word_174_congr v w (H0 : word_121 v = word_121 w) : word_174 v = word_174 w.
Proof. unfold word_174, closed_word_174. rewrite H0. reflexivity. Qed.
Lemma word_174_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_174 v = word_174 w.
Proof. apply word_174_congr.
 - apply word_121_inputs; assumption.
Qed.
Lemma word_175_congr v w (H0 : word_173 v = word_173 w) (H1 : word_174 v = word_174 w) : word_175 v = word_175 w.
Proof. unfold word_175, closed_word_175. rewrite H0 H1. reflexivity. Qed.
Lemma word_175_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_175 v = word_175 w.
Proof. apply word_175_congr.
 - apply word_173_inputs; assumption.
 - apply word_174_inputs; assumption.
Qed.
Lemma word_176_congr v w (H0 : word_121 v = word_121 w) : word_176 v = word_176 w.
Proof. unfold word_176, closed_word_176. rewrite H0. reflexivity. Qed.
Lemma word_176_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_176 v = word_176 w.
Proof. apply word_176_congr.
 - apply word_121_inputs; assumption.
Qed.
Lemma word_177_congr v w (H0 : word_175 v = word_175 w) (H1 : word_176 v = word_176 w) : word_177 v = word_177 w.
Proof. unfold word_177, closed_word_177. rewrite H0 H1. reflexivity. Qed.
Lemma word_177_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_177 v = word_177 w.
Proof. apply word_177_congr.
 - apply word_175_inputs; assumption.
 - apply word_176_inputs; assumption.
Qed.
Lemma word_178_congr v w (H0 : word_171 v = word_171 w) : word_178 v = word_178 w.
Proof. unfold word_178, closed_word_178. rewrite H0. reflexivity. Qed.
Lemma word_178_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_178 v = word_178 w.
Proof. apply word_178_congr.
 - apply word_171_inputs; assumption.
Qed.
Lemma word_179_congr v w (H0 : word_170 v = word_170 w) (H1 : word_178 v = word_178 w) : word_179 v = word_179 w.
Proof. unfold word_179, closed_word_179. rewrite H0 H1. reflexivity. Qed.
Lemma word_179_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_179 v = word_179 w.
Proof. apply word_179_congr.
 - apply word_170_inputs; assumption.
 - apply word_178_inputs; assumption.
Qed.
Lemma word_180_congr v w (H0 : word_177 v = word_177 w) (H1 : word_179 v = word_179 w) : word_180 v = word_180 w.
Proof. unfold word_180, closed_word_180. rewrite H0 H1. reflexivity. Qed.
Lemma word_180_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_180 v = word_180 w.
Proof. apply word_180_congr.
 - apply word_177_inputs; assumption.
 - apply word_179_inputs; assumption.
Qed.
Lemma word_181_congr v w (H0 : word_180 v = word_180 w) : word_181 v = word_181 w.
Proof. unfold word_181, closed_word_181. rewrite H0. reflexivity. Qed.
Lemma word_181_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_181 v = word_181 w.
Proof. apply word_181_congr.
 - apply word_180_inputs; assumption.
Qed.
Lemma word_182_congr v w (H0 : word_180 v = word_180 w) : word_182 v = word_182 w.
Proof. unfold word_182, closed_word_182. rewrite H0. reflexivity. Qed.
Lemma word_182_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_182 v = word_182 w.
Proof. apply word_182_congr.
 - apply word_180_inputs; assumption.
Qed.
Lemma word_183_congr v w (H0 : word_180 v = word_180 w) : word_183 v = word_183 w.
Proof. unfold word_183, closed_word_183. rewrite H0. reflexivity. Qed.
Lemma word_183_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_183 v = word_183 w.
Proof. apply word_183_congr.
 - apply word_180_inputs; assumption.
Qed.
Lemma word_184_congr v w (H0 : word_180 v = word_180 w) : word_184 v = word_184 w.
Proof. unfold word_184, closed_word_184. rewrite H0. reflexivity. Qed.
Lemma word_184_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_184 v = word_184 w.
Proof. apply word_184_congr.
 - apply word_180_inputs; assumption.
Qed.
Lemma word_185_congr v w (H0 : word_180 v = word_180 w) : word_185 v = word_185 w.
Proof. unfold word_185, closed_word_185. rewrite H0. reflexivity. Qed.
Lemma word_185_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_185 v = word_185 w.
Proof. apply word_185_congr.
 - apply word_180_inputs; assumption.
Qed.
Lemma word_186_congr v w (H0 : word_180 v = word_180 w) : word_186 v = word_186 w.
Proof. unfold word_186, closed_word_186. rewrite H0. reflexivity. Qed.
Lemma word_186_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_186 v = word_186 w.
Proof. apply word_186_congr.
 - apply word_180_inputs; assumption.
Qed.
Lemma word_187_congr v w (H0 : word_180 v = word_180 w) : word_187 v = word_187 w.
Proof. unfold word_187, closed_word_187. rewrite H0. reflexivity. Qed.
Lemma word_187_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_187 v = word_187 w.
Proof. apply word_187_congr.
 - apply word_180_inputs; assumption.
Qed.
Lemma word_188_congr v w (H0 : word_180 v = word_180 w) : word_188 v = word_188 w.
Proof. unfold word_188, closed_word_188. rewrite H0. reflexivity. Qed.
Lemma word_188_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_188 v = word_188 w.
Proof. apply word_188_congr.
 - apply word_180_inputs; assumption.
Qed.
Lemma word_189_congr v w (H0 : word_180 v = word_180 w) : word_189 v = word_189 w.
Proof. unfold word_189, closed_word_189. rewrite H0. reflexivity. Qed.
Lemma word_189_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_189 v = word_189 w.
Proof. apply word_189_congr.
 - apply word_180_inputs; assumption.
Qed.
Lemma word_190_congr v w (H0 : word_180 v = word_180 w) : word_190 v = word_190 w.
Proof. unfold word_190, closed_word_190. rewrite H0. reflexivity. Qed.
Lemma word_190_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_190 v = word_190 w.
Proof. apply word_190_congr.
 - apply word_180_inputs; assumption.
Qed.
Lemma word_191_congr v w (H0 : word_180 v = word_180 w) : word_191 v = word_191 w.
Proof. unfold word_191, closed_word_191. rewrite H0. reflexivity. Qed.
Lemma word_191_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_191 v = word_191 w.
Proof. apply word_191_congr.
 - apply word_180_inputs; assumption.
Qed.
Lemma word_192_congr v w (H0 : word_180 v = word_180 w) : word_192 v = word_192 w.
Proof. unfold word_192, closed_word_192. rewrite H0. reflexivity. Qed.
Lemma word_192_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_192 v = word_192 w.
Proof. apply word_192_congr.
 - apply word_180_inputs; assumption.
Qed.
Lemma word_193_congr v w (H0 : word_158 v = word_158 w) : word_193 v = word_193 w.
Proof. unfold word_193, closed_word_193. rewrite H0. reflexivity. Qed.
Lemma word_193_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_193 v = word_193 w.
Proof. apply word_193_congr.
 - apply word_158_inputs; assumption.
Qed.
Lemma word_194_congr v w (H0 : word_193 v = word_193 w) : word_194 v = word_194 w.
Proof. unfold word_194, closed_word_194. rewrite H0. reflexivity. Qed.
Lemma word_194_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_194 v = word_194 w.
Proof. apply word_194_congr.
 - apply word_193_inputs; assumption.
Qed.
Lemma word_195_congr v w (H0 : word_158 v = word_158 w) : word_195 v = word_195 w.
Proof. unfold word_195, closed_word_195. rewrite H0. reflexivity. Qed.
Lemma word_195_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_195 v = word_195 w.
Proof. apply word_195_congr.
 - apply word_158_inputs; assumption.
Qed.
Lemma word_196_congr v w (H0 : word_194 v = word_194 w) (H1 : word_195 v = word_195 w) : word_196 v = word_196 w.
Proof. unfold word_196, closed_word_196. rewrite H0 H1. reflexivity. Qed.
Lemma word_196_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_196 v = word_196 w.
Proof. apply word_196_congr.
 - apply word_194_inputs; assumption.
 - apply word_195_inputs; assumption.
Qed.
Lemma word_197_congr v w (H0 : word_158 v = word_158 w) : word_197 v = word_197 w.
Proof. unfold word_197, closed_word_197. rewrite H0. reflexivity. Qed.
Lemma word_197_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_197 v = word_197 w.
Proof. apply word_197_congr.
 - apply word_158_inputs; assumption.
Qed.
Lemma word_198_congr v w (H0 : word_196 v = word_196 w) (H1 : word_197 v = word_197 w) : word_198 v = word_198 w.
Proof. unfold word_198, closed_word_198. rewrite H0 H1. reflexivity. Qed.
Lemma word_198_inputs v w (Ha : v 0 2 = w 0 2) (Hb : v 0 3 = w 0 3) : word_198 v = word_198 w.
Proof. apply word_198_congr.
 - apply word_196_inputs; assumption.
 - apply word_197_inputs; assumption.
Qed.
