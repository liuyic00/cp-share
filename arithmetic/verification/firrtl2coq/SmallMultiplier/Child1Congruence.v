From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From SmallMultiplier Require Import Child1Stable.
Local Open Scope N_scope.
Lemma word_7_congr v w (H0 : word_2 v = word_2 w) : word_7 v = word_7 w.
Proof. unfold word_7, closed_word_7. rewrite H0. reflexivity. Qed.
Lemma word_7_inputs v w (I0 : v 0 2 = w 0 2) : word_7 v = word_7 w.
Proof. apply word_7_congr.
 - assumption.
Qed.
Lemma word_8_congr v w (H0 : word_3 v = word_3 w) : word_8 v = word_8 w.
Proof. unfold word_8, closed_word_8. rewrite H0. reflexivity. Qed.
Lemma word_8_inputs v w (I0 : v 0 3 = w 0 3) : word_8 v = word_8 w.
Proof. apply word_8_congr.
 - assumption.
Qed.
Lemma word_9_congr v w (H0 : word_4 v = word_4 w) : word_9 v = word_9 w.
Proof. unfold word_9, closed_word_9. rewrite H0. reflexivity. Qed.
Lemma word_9_inputs v w (I0 : v 0 4 = w 0 4) : word_9 v = word_9 w.
Proof. apply word_9_congr.
 - assumption.
Qed.
Lemma word_10_congr v w (H0 : word_7 v = word_7 w) (H1 : word_8 v = word_8 w) : word_10 v = word_10 w.
Proof. unfold word_10, closed_word_10. rewrite H0 H1. reflexivity. Qed.
Lemma word_10_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) : word_10 v = word_10 w.
Proof. apply word_10_congr.
 - apply word_7_inputs; assumption.
 - apply word_8_inputs; assumption.
Qed.
Lemma word_11_congr v w (H0 : word_10 v = word_10 w) : word_11 v = word_11 w.
Proof. unfold word_11, closed_word_11. rewrite H0. reflexivity. Qed.
Lemma word_11_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) : word_11 v = word_11 w.
Proof. apply word_11_congr.
 - apply word_10_inputs; assumption.
Qed.
Lemma word_12_congr v w (H0 : word_9 v = word_9 w) (H1 : word_11 v = word_11 w) : word_12 v = word_12 w.
Proof. unfold word_12, closed_word_12. rewrite H0 H1. reflexivity. Qed.
Lemma word_12_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) (I2 : v 0 4 = w 0 4) : word_12 v = word_12 w.
Proof. apply word_12_congr.
 - apply word_9_inputs; assumption.
 - apply word_11_inputs; assumption.
Qed.
Lemma word_13_congr v w (H0 : word_12 v = word_12 w) : word_13 v = word_13 w.
Proof. unfold word_13, closed_word_13. rewrite H0. reflexivity. Qed.
Lemma word_13_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) (I2 : v 0 4 = w 0 4) : word_13 v = word_13 w.
Proof. apply word_13_congr.
 - apply word_12_inputs; assumption.
Qed.
Lemma word_25_congr v w (H0 : word_4 v = word_4 w) : word_25 v = word_25 w.
Proof. unfold word_25, closed_word_25. rewrite H0. reflexivity. Qed.
Lemma word_25_inputs v w (I0 : v 0 4 = w 0 4) : word_25 v = word_25 w.
Proof. apply word_25_congr.
 - assumption.
Qed.
Lemma word_23_congr v w (H0 : word_2 v = word_2 w) : word_23 v = word_23 w.
Proof. unfold word_23, closed_word_23. rewrite H0. reflexivity. Qed.
Lemma word_23_inputs v w (I0 : v 0 2 = w 0 2) : word_23 v = word_23 w.
Proof. apply word_23_congr.
 - assumption.
Qed.
Lemma word_24_congr v w (H0 : word_3 v = word_3 w) : word_24 v = word_24 w.
Proof. unfold word_24, closed_word_24. rewrite H0. reflexivity. Qed.
Lemma word_24_inputs v w (I0 : v 0 3 = w 0 3) : word_24 v = word_24 w.
Proof. apply word_24_congr.
 - assumption.
Qed.
Lemma word_26_congr v w (H0 : word_23 v = word_23 w) (H1 : word_24 v = word_24 w) : word_26 v = word_26 w.
Proof. unfold word_26, closed_word_26. rewrite H0 H1. reflexivity. Qed.
Lemma word_26_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) : word_26 v = word_26 w.
Proof. apply word_26_congr.
 - apply word_23_inputs; assumption.
 - apply word_24_inputs; assumption.
Qed.
Lemma word_28_congr v w (H0 : word_25 v = word_25 w) (H1 : word_26 v = word_26 w) : word_28 v = word_28 w.
Proof. unfold word_28, closed_word_28. rewrite H0 H1. reflexivity. Qed.
Lemma word_28_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) (I2 : v 0 4 = w 0 4) : word_28 v = word_28 w.
Proof. apply word_28_congr.
 - apply word_25_inputs; assumption.
 - apply word_26_inputs; assumption.
Qed.
Lemma word_27_congr v w (H0 : word_23 v = word_23 w) (H1 : word_24 v = word_24 w) : word_27 v = word_27 w.
Proof. unfold word_27, closed_word_27. rewrite H0 H1. reflexivity. Qed.
Lemma word_27_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) : word_27 v = word_27 w.
Proof. apply word_27_congr.
 - apply word_23_inputs; assumption.
 - apply word_24_inputs; assumption.
Qed.
Lemma word_29_congr v w (H0 : word_25 v = word_25 w) (H1 : word_26 v = word_26 w) : word_29 v = word_29 w.
Proof. unfold word_29, closed_word_29. rewrite H0 H1. reflexivity. Qed.
Lemma word_29_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) (I2 : v 0 4 = w 0 4) : word_29 v = word_29 w.
Proof. apply word_29_congr.
 - apply word_25_inputs; assumption.
 - apply word_26_inputs; assumption.
Qed.
Lemma word_30_congr v w (H0 : word_27 v = word_27 w) (H1 : word_29 v = word_29 w) : word_30 v = word_30 w.
Proof. unfold word_30, closed_word_30. rewrite H0 H1. reflexivity. Qed.
Lemma word_30_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) (I2 : v 0 4 = w 0 4) : word_30 v = word_30 w.
Proof. apply word_30_congr.
 - apply word_27_inputs; assumption.
 - apply word_29_inputs; assumption.
Qed.
Lemma word_31_congr v w (H0 : word_28 v = word_28 w) (H1 : word_30 v = word_30 w) : word_31 v = word_31 w.
Proof. unfold word_31, closed_word_31. rewrite H0 H1. reflexivity. Qed.
Lemma word_31_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) (I2 : v 0 4 = w 0 4) : word_31 v = word_31 w.
Proof. apply word_31_congr.
 - apply word_28_inputs; assumption.
 - apply word_30_inputs; assumption.
Qed.
Lemma word_32_congr v w (H0 : word_31 v = word_31 w) : word_32 v = word_32 w.
Proof. unfold word_32, closed_word_32. rewrite H0. reflexivity. Qed.
Lemma word_32_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) (I2 : v 0 4 = w 0 4) : word_32 v = word_32 w.
Proof. apply word_32_congr.
 - apply word_31_inputs; assumption.
Qed.
Lemma word_33_congr v w (H0 : word_32 v = word_32 w) : word_33 v = word_33 w.
Proof. unfold word_33, closed_word_33. rewrite H0. reflexivity. Qed.
Lemma word_33_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) (I2 : v 0 4 = w 0 4) : word_33 v = word_33 w.
Proof. apply word_33_congr.
 - apply word_32_inputs; assumption.
Qed.
Lemma word_5_congr v w (H0 : word_33 v = word_33 w) : word_5 v = word_5 w.
Proof. unfold word_5, closed_word_5. rewrite H0. reflexivity. Qed.
Lemma word_5_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) (I2 : v 0 4 = w 0 4) : word_5 v = word_5 w.
Proof. apply word_5_congr.
 - apply word_33_inputs; assumption.
Qed.
Lemma word_14_congr v w (H0 : word_5 v = word_5 w) : word_14 v = word_14 w.
Proof. unfold word_14, closed_word_14. rewrite H0. reflexivity. Qed.
Lemma word_14_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) (I2 : v 0 4 = w 0 4) : word_14 v = word_14 w.
Proof. apply word_14_congr.
 - apply word_5_inputs; assumption.
Qed.
Lemma word_34_congr v w (H0 : word_32 v = word_32 w) : word_34 v = word_34 w.
Proof. unfold word_34, closed_word_34. rewrite H0. reflexivity. Qed.
Lemma word_34_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) (I2 : v 0 4 = w 0 4) : word_34 v = word_34 w.
Proof. apply word_34_congr.
 - apply word_32_inputs; assumption.
Qed.
Lemma word_6_congr v w (H0 : word_34 v = word_34 w) : word_6 v = word_6 w.
Proof. unfold word_6, closed_word_6. rewrite H0. reflexivity. Qed.
Lemma word_6_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) (I2 : v 0 4 = w 0 4) : word_6 v = word_6 w.
Proof. apply word_6_congr.
 - apply word_34_inputs; assumption.
Qed.
Lemma word_15_congr v w (H0 : word_6 v = word_6 w) : word_15 v = word_15 w.
Proof. unfold word_15, closed_word_15. rewrite H0. reflexivity. Qed.
Lemma word_15_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) (I2 : v 0 4 = w 0 4) : word_15 v = word_15 w.
Proof. apply word_15_congr.
 - apply word_6_inputs; assumption.
Qed.
Lemma word_16_congr v w (H0 : word_15 v = word_15 w) : word_16 v = word_16 w.
Proof. unfold word_16, closed_word_16. rewrite H0. reflexivity. Qed.
Lemma word_16_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) (I2 : v 0 4 = w 0 4) : word_16 v = word_16 w.
Proof. apply word_16_congr.
 - apply word_15_inputs; assumption.
Qed.
Lemma word_17_congr v w (H0 : word_14 v = word_14 w) (H1 : word_16 v = word_16 w) : word_17 v = word_17 w.
Proof. unfold word_17, closed_word_17. rewrite H0 H1. reflexivity. Qed.
Lemma word_17_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) (I2 : v 0 4 = w 0 4) : word_17 v = word_17 w.
Proof. apply word_17_congr.
 - apply word_14_inputs; assumption.
 - apply word_16_inputs; assumption.
Qed.
Lemma word_18_congr v w (H0 : word_17 v = word_17 w) : word_18 v = word_18 w.
Proof. unfold word_18, closed_word_18. rewrite H0. reflexivity. Qed.
Lemma word_18_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) (I2 : v 0 4 = w 0 4) : word_18 v = word_18 w.
Proof. apply word_18_congr.
 - apply word_17_inputs; assumption.
Qed.
Lemma word_19_congr v w (H0 : word_13 v = word_13 w) (H1 : word_18 v = word_18 w) : word_19 v = word_19 w.
Proof. unfold word_19, closed_word_19. rewrite H0 H1. reflexivity. Qed.
Lemma word_19_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) (I2 : v 0 4 = w 0 4) : word_19 v = word_19 w.
Proof. apply word_19_congr.
 - apply word_13_inputs; assumption.
 - apply word_18_inputs; assumption.
Qed.
Lemma word_20_congr v w (H0 : word_1 v = word_1 w) : word_20 v = word_20 w.
Proof. unfold word_20, closed_word_20. rewrite H0. reflexivity. Qed.
Lemma word_20_inputs v w (I0 : v 0 1 = w 0 1) : word_20 v = word_20 w.
Proof. apply word_20_congr.
 - assumption.
Qed.
Lemma word_21_congr v w (H0 : word_20 v = word_20 w) : word_21 v = word_21 w.
Proof. unfold word_21, closed_word_21. rewrite H0. reflexivity. Qed.
Lemma word_21_inputs v w (I0 : v 0 1 = w 0 1) : word_21 v = word_21 w.
Proof. apply word_21_congr.
 - apply word_20_inputs; assumption.
Qed.
Lemma word_22_congr v w (H0 : word_19 v = word_19 w) : word_22 v = word_22 w.
Proof. unfold word_22, closed_word_22. rewrite H0. reflexivity. Qed.
Lemma word_22_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) (I2 : v 0 4 = w 0 4) : word_22 v = word_22 w.
Proof. apply word_22_congr.
 - apply word_19_inputs; assumption.
Qed.
