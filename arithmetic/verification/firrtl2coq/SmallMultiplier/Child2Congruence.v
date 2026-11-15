From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From SmallMultiplier Require Import Child2Stable.
Local Open Scope N_scope.
Lemma word_12_congr v w (H0 : word_2 v = word_2 w) : word_12 v = word_12 w.
Proof. unfold word_12, closed_word_12. rewrite H0. reflexivity. Qed.
Lemma word_12_inputs v w (I0 : v 0 2 = w 0 2) : word_12 v = word_12 w.
Proof. apply word_12_congr.
 - assumption.
Qed.
Lemma word_13_congr v w (H0 : word_3 v = word_3 w) : word_13 v = word_13 w.
Proof. unfold word_13, closed_word_13. rewrite H0. reflexivity. Qed.
Lemma word_13_inputs v w (I0 : v 0 3 = w 0 3) : word_13 v = word_13 w.
Proof. apply word_13_congr.
 - assumption.
Qed.
Lemma word_14_congr v w (H0 : word_4 v = word_4 w) : word_14 v = word_14 w.
Proof. unfold word_14, closed_word_14. rewrite H0. reflexivity. Qed.
Lemma word_14_inputs v w (I0 : v 0 4 = w 0 4) : word_14 v = word_14 w.
Proof. apply word_14_congr.
 - assumption.
Qed.
Lemma word_15_congr v w (H0 : word_5 v = word_5 w) : word_15 v = word_15 w.
Proof. unfold word_15, closed_word_15. rewrite H0. reflexivity. Qed.
Lemma word_15_inputs v w (I0 : v 0 5 = w 0 5) : word_15 v = word_15 w.
Proof. apply word_15_congr.
 - assumption.
Qed.
Lemma word_16_congr v w (H0 : word_6 v = word_6 w) : word_16 v = word_16 w.
Proof. unfold word_16, closed_word_16. rewrite H0. reflexivity. Qed.
Lemma word_16_inputs v w (I0 : v 0 6 = w 0 6) : word_16 v = word_16 w.
Proof. apply word_16_congr.
 - assumption.
Qed.
Lemma word_17_congr v w (H0 : word_12 v = word_12 w) (H1 : word_13 v = word_13 w) : word_17 v = word_17 w.
Proof. unfold word_17, closed_word_17. rewrite H0 H1. reflexivity. Qed.
Lemma word_17_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) : word_17 v = word_17 w.
Proof. apply word_17_congr.
 - apply word_12_inputs; assumption.
 - apply word_13_inputs; assumption.
Qed.
Lemma word_18_congr v w (H0 : word_17 v = word_17 w) : word_18 v = word_18 w.
Proof. unfold word_18, closed_word_18. rewrite H0. reflexivity. Qed.
Lemma word_18_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) : word_18 v = word_18 w.
Proof. apply word_18_congr.
 - apply word_17_inputs; assumption.
Qed.
Lemma word_19_congr v w (H0 : word_14 v = word_14 w) (H1 : word_18 v = word_18 w) : word_19 v = word_19 w.
Proof. unfold word_19, closed_word_19. rewrite H0 H1. reflexivity. Qed.
Lemma word_19_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) (I2 : v 0 4 = w 0 4) : word_19 v = word_19 w.
Proof. apply word_19_congr.
 - apply word_14_inputs; assumption.
 - apply word_18_inputs; assumption.
Qed.
Lemma word_20_congr v w (H0 : word_19 v = word_19 w) : word_20 v = word_20 w.
Proof. unfold word_20, closed_word_20. rewrite H0. reflexivity. Qed.
Lemma word_20_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) (I2 : v 0 4 = w 0 4) : word_20 v = word_20 w.
Proof. apply word_20_congr.
 - apply word_19_inputs; assumption.
Qed.
Lemma word_21_congr v w (H0 : word_15 v = word_15 w) (H1 : word_20 v = word_20 w) : word_21 v = word_21 w.
Proof. unfold word_21, closed_word_21. rewrite H0 H1. reflexivity. Qed.
Lemma word_21_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) (I2 : v 0 4 = w 0 4) (I3 : v 0 5 = w 0 5) : word_21 v = word_21 w.
Proof. apply word_21_congr.
 - apply word_15_inputs; assumption.
 - apply word_20_inputs; assumption.
Qed.
Lemma word_22_congr v w (H0 : word_21 v = word_21 w) : word_22 v = word_22 w.
Proof. unfold word_22, closed_word_22. rewrite H0. reflexivity. Qed.
Lemma word_22_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) (I2 : v 0 4 = w 0 4) (I3 : v 0 5 = w 0 5) : word_22 v = word_22 w.
Proof. apply word_22_congr.
 - apply word_21_inputs; assumption.
Qed.
Lemma word_23_congr v w (H0 : word_16 v = word_16 w) (H1 : word_22 v = word_22 w) : word_23 v = word_23 w.
Proof. unfold word_23, closed_word_23. rewrite H0 H1. reflexivity. Qed.
Lemma word_23_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) (I2 : v 0 4 = w 0 4) (I3 : v 0 5 = w 0 5) (I4 : v 0 6 = w 0 6) : word_23 v = word_23 w.
Proof. apply word_23_congr.
 - apply word_16_inputs; assumption.
 - apply word_22_inputs; assumption.
Qed.
Lemma word_24_congr v w (H0 : word_23 v = word_23 w) : word_24 v = word_24 w.
Proof. unfold word_24, closed_word_24. rewrite H0. reflexivity. Qed.
Lemma word_24_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) (I2 : v 0 4 = w 0 4) (I3 : v 0 5 = w 0 5) (I4 : v 0 6 = w 0 6) : word_24 v = word_24 w.
Proof. apply word_24_congr.
 - apply word_23_inputs; assumption.
Qed.
Lemma word_41_congr v w (H0 : port_11_5 v = port_11_5 w) : word_41 v = word_41 w.
Proof. unfold word_41, closed_word_41. rewrite H0. reflexivity. Qed.
Lemma word_41_inputs v w (I0 : v 11 5 = w 11 5) : word_41 v = word_41 w.
Proof. apply word_41_congr.
 - assumption.
Qed.
Lemma word_7_congr v w (H0 : word_41 v = word_41 w) : word_7 v = word_7 w.
Proof. unfold word_7, closed_word_7. rewrite H0. reflexivity. Qed.
Lemma word_7_inputs v w (I0 : v 11 5 = w 11 5) : word_7 v = word_7 w.
Proof. apply word_7_congr.
 - apply word_41_inputs; assumption.
Qed.
Lemma word_25_congr v w (H0 : word_7 v = word_7 w) : word_25 v = word_25 w.
Proof. unfold word_25, closed_word_25. rewrite H0. reflexivity. Qed.
Lemma word_25_inputs v w (I0 : v 11 5 = w 11 5) : word_25 v = word_25 w.
Proof. apply word_25_congr.
 - apply word_7_inputs; assumption.
Qed.
Lemma word_42_congr v w (H0 : port_10_6 v = port_10_6 w) : word_42 v = word_42 w.
Proof. unfold word_42, closed_word_42. rewrite H0. reflexivity. Qed.
Lemma word_42_inputs v w (I0 : v 10 6 = w 10 6) : word_42 v = word_42 w.
Proof. apply word_42_congr.
 - assumption.
Qed.
Lemma word_8_congr v w (H0 : word_42 v = word_42 w) : word_8 v = word_8 w.
Proof. unfold word_8, closed_word_8. rewrite H0. reflexivity. Qed.
Lemma word_8_inputs v w (I0 : v 10 6 = w 10 6) : word_8 v = word_8 w.
Proof. apply word_8_congr.
 - apply word_42_inputs; assumption.
Qed.
Lemma word_26_congr v w (H0 : word_8 v = word_8 w) : word_26 v = word_26 w.
Proof. unfold word_26, closed_word_26. rewrite H0. reflexivity. Qed.
Lemma word_26_inputs v w (I0 : v 10 6 = w 10 6) : word_26 v = word_26 w.
Proof. apply word_26_congr.
 - apply word_8_inputs; assumption.
Qed.
Lemma word_27_congr v w (H0 : word_26 v = word_26 w) : word_27 v = word_27 w.
Proof. unfold word_27, closed_word_27. rewrite H0. reflexivity. Qed.
Lemma word_27_inputs v w (I0 : v 10 6 = w 10 6) : word_27 v = word_27 w.
Proof. apply word_27_congr.
 - apply word_26_inputs; assumption.
Qed.
Lemma word_43_congr v w (H0 : port_11_6 v = port_11_6 w) : word_43 v = word_43 w.
Proof. unfold word_43, closed_word_43. rewrite H0. reflexivity. Qed.
Lemma word_43_inputs v w (I0 : v 11 6 = w 11 6) : word_43 v = word_43 w.
Proof. apply word_43_congr.
 - assumption.
Qed.
Lemma word_9_congr v w (H0 : word_43 v = word_43 w) : word_9 v = word_9 w.
Proof. unfold word_9, closed_word_9. rewrite H0. reflexivity. Qed.
Lemma word_9_inputs v w (I0 : v 11 6 = w 11 6) : word_9 v = word_9 w.
Proof. apply word_9_congr.
 - apply word_43_inputs; assumption.
Qed.
Lemma word_28_congr v w (H0 : word_9 v = word_9 w) : word_28 v = word_28 w.
Proof. unfold word_28, closed_word_28. rewrite H0. reflexivity. Qed.
Lemma word_28_inputs v w (I0 : v 11 6 = w 11 6) : word_28 v = word_28 w.
Proof. apply word_28_congr.
 - apply word_9_inputs; assumption.
Qed.
Lemma word_29_congr v w (H0 : word_28 v = word_28 w) : word_29 v = word_29 w.
Proof. unfold word_29, closed_word_29. rewrite H0. reflexivity. Qed.
Lemma word_29_inputs v w (I0 : v 11 6 = w 11 6) : word_29 v = word_29 w.
Proof. apply word_29_congr.
 - apply word_28_inputs; assumption.
Qed.
Lemma word_30_congr v w (H0 : word_25 v = word_25 w) (H1 : word_27 v = word_27 w) : word_30 v = word_30 w.
Proof. unfold word_30, closed_word_30. rewrite H0 H1. reflexivity. Qed.
Lemma word_30_inputs v w (I0 : v 10 6 = w 10 6) (I1 : v 11 5 = w 11 5) : word_30 v = word_30 w.
Proof. apply word_30_congr.
 - apply word_25_inputs; assumption.
 - apply word_27_inputs; assumption.
Qed.
Lemma word_31_congr v w (H0 : word_30 v = word_30 w) : word_31 v = word_31 w.
Proof. unfold word_31, closed_word_31. rewrite H0. reflexivity. Qed.
Lemma word_31_inputs v w (I0 : v 10 6 = w 10 6) (I1 : v 11 5 = w 11 5) : word_31 v = word_31 w.
Proof. apply word_31_congr.
 - apply word_30_inputs; assumption.
Qed.
Lemma word_32_congr v w (H0 : word_29 v = word_29 w) (H1 : word_31 v = word_31 w) : word_32 v = word_32 w.
Proof. unfold word_32, closed_word_32. rewrite H0 H1. reflexivity. Qed.
Lemma word_32_inputs v w (I0 : v 10 6 = w 10 6) (I1 : v 11 5 = w 11 5) (I2 : v 11 6 = w 11 6) : word_32 v = word_32 w.
Proof. apply word_32_congr.
 - apply word_29_inputs; assumption.
 - apply word_31_inputs; assumption.
Qed.
Lemma word_33_congr v w (H0 : word_32 v = word_32 w) : word_33 v = word_33 w.
Proof. unfold word_33, closed_word_33. rewrite H0. reflexivity. Qed.
Lemma word_33_inputs v w (I0 : v 10 6 = w 10 6) (I1 : v 11 5 = w 11 5) (I2 : v 11 6 = w 11 6) : word_33 v = word_33 w.
Proof. apply word_33_congr.
 - apply word_32_inputs; assumption.
Qed.
Lemma word_34_congr v w (H0 : word_24 v = word_24 w) (H1 : word_33 v = word_33 w) : word_34 v = word_34 w.
Proof. unfold word_34, closed_word_34. rewrite H0 H1. reflexivity. Qed.
Lemma word_34_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) (I2 : v 0 4 = w 0 4) (I3 : v 0 5 = w 0 5) (I4 : v 0 6 = w 0 6) (I5 : v 10 6 = w 10 6) (I6 : v 11 5 = w 11 5) (I7 : v 11 6 = w 11 6) : word_34 v = word_34 w.
Proof. apply word_34_congr.
 - apply word_24_inputs; assumption.
 - apply word_33_inputs; assumption.
Qed.
Lemma word_35_congr v w (H0 : word_1 v = word_1 w) : word_35 v = word_35 w.
Proof. unfold word_35, closed_word_35. rewrite H0. reflexivity. Qed.
Lemma word_35_inputs v w (I0 : v 0 1 = w 0 1) : word_35 v = word_35 w.
Proof. apply word_35_congr.
 - assumption.
Qed.
Lemma word_36_congr v w (H0 : word_35 v = word_35 w) : word_36 v = word_36 w.
Proof. unfold word_36, closed_word_36. rewrite H0. reflexivity. Qed.
Lemma word_36_inputs v w (I0 : v 0 1 = w 0 1) : word_36 v = word_36 w.
Proof. apply word_36_congr.
 - apply word_35_inputs; assumption.
Qed.
Lemma word_37_congr v w (H0 : word_34 v = word_34 w) : word_37 v = word_37 w.
Proof. unfold word_37, closed_word_37. rewrite H0. reflexivity. Qed.
Lemma word_37_inputs v w (I0 : v 0 2 = w 0 2) (I1 : v 0 3 = w 0 3) (I2 : v 0 4 = w 0 4) (I3 : v 0 5 = w 0 5) (I4 : v 0 6 = w 0 6) (I5 : v 10 6 = w 10 6) (I6 : v 11 5 = w 11 5) (I7 : v 11 6 = w 11 6) : word_37 v = word_37 w.
Proof. apply word_37_congr.
 - apply word_34_inputs; assumption.
Qed.
Lemma word_38_congr v w (H0 : port_10_5 v = port_10_5 w) : word_38 v = word_38 w.
Proof. unfold word_38, closed_word_38. rewrite H0. reflexivity. Qed.
Lemma word_38_inputs v w (I0 : v 10 5 = w 10 5) : word_38 v = word_38 w.
Proof. apply word_38_congr.
 - assumption.
Qed.
Lemma word_39_congr v w (H0 : word_5 v = word_5 w) : word_39 v = word_39 w.
Proof. unfold word_39, closed_word_39. rewrite H0. reflexivity. Qed.
Lemma word_39_inputs v w (I0 : v 0 5 = w 0 5) : word_39 v = word_39 w.
Proof. apply word_39_congr.
 - assumption.
Qed.
Lemma word_40_congr v w (H0 : word_6 v = word_6 w) : word_40 v = word_40 w.
Proof. unfold word_40, closed_word_40. rewrite H0. reflexivity. Qed.
Lemma word_40_inputs v w (I0 : v 0 6 = w 0 6) : word_40 v = word_40 w.
Proof. apply word_40_congr.
 - assumption.
Qed.
Lemma port_10_0_congr v w (H0 : word_0 v = word_0 w) : port_10_0 v = port_10_0 w.
Proof. unfold port_10_0, closed_port_10_0. rewrite H0. reflexivity. Qed.
Lemma port_10_0_inputs v w (I0 : v 0 0 = w 0 0) : port_10_0 v = port_10_0 w.
Proof. apply port_10_0_congr.
 - assumption.
Qed.
Lemma port_10_1_congr v w (H0 : word_1 v = word_1 w) : port_10_1 v = port_10_1 w.
Proof. unfold port_10_1, closed_port_10_1. rewrite H0. reflexivity. Qed.
Lemma port_10_1_inputs v w (I0 : v 0 1 = w 0 1) : port_10_1 v = port_10_1 w.
Proof. apply port_10_1_congr.
 - assumption.
Qed.
Lemma port_10_2_congr v w (H0 : word_2 v = word_2 w) : port_10_2 v = port_10_2 w.
Proof. unfold port_10_2, closed_port_10_2. rewrite H0. reflexivity. Qed.
Lemma port_10_2_inputs v w (I0 : v 0 2 = w 0 2) : port_10_2 v = port_10_2 w.
Proof. apply port_10_2_congr.
 - assumption.
Qed.
Lemma port_10_3_congr v w (H0 : word_3 v = word_3 w) : port_10_3 v = port_10_3 w.
Proof. unfold port_10_3, closed_port_10_3. rewrite H0. reflexivity. Qed.
Lemma port_10_3_inputs v w (I0 : v 0 3 = w 0 3) : port_10_3 v = port_10_3 w.
Proof. apply port_10_3_congr.
 - assumption.
Qed.
Lemma port_10_4_congr v w (H0 : word_4 v = word_4 w) : port_10_4 v = port_10_4 w.
Proof. unfold port_10_4, closed_port_10_4. rewrite H0. reflexivity. Qed.
Lemma port_10_4_inputs v w (I0 : v 0 4 = w 0 4) : port_10_4 v = port_10_4 w.
Proof. apply port_10_4_congr.
 - assumption.
Qed.
Lemma port_11_0_congr v w (H0 : word_0 v = word_0 w) : port_11_0 v = port_11_0 w.
Proof. unfold port_11_0, closed_port_11_0. rewrite H0. reflexivity. Qed.
Lemma port_11_0_inputs v w (I0 : v 0 0 = w 0 0) : port_11_0 v = port_11_0 w.
Proof. apply port_11_0_congr.
 - assumption.
Qed.
Lemma port_11_1_congr v w (H0 : word_1 v = word_1 w) : port_11_1 v = port_11_1 w.
Proof. unfold port_11_1, closed_port_11_1. rewrite H0. reflexivity. Qed.
Lemma port_11_1_inputs v w (I0 : v 0 1 = w 0 1) : port_11_1 v = port_11_1 w.
Proof. apply port_11_1_congr.
 - assumption.
Qed.
Lemma port_11_2_congr v w (H0 : word_38 v = word_38 w) : port_11_2 v = port_11_2 w.
Proof. unfold port_11_2, closed_port_11_2. rewrite H0. reflexivity. Qed.
Lemma port_11_2_inputs v w (I0 : v 10 5 = w 10 5) : port_11_2 v = port_11_2 w.
Proof. apply port_11_2_congr.
 - apply word_38_inputs; assumption.
Qed.
Lemma port_11_3_congr v w (H0 : word_39 v = word_39 w) : port_11_3 v = port_11_3 w.
Proof. unfold port_11_3, closed_port_11_3. rewrite H0. reflexivity. Qed.
Lemma port_11_3_inputs v w (I0 : v 0 5 = w 0 5) : port_11_3 v = port_11_3 w.
Proof. apply port_11_3_congr.
 - apply word_39_inputs; assumption.
Qed.
Lemma port_11_4_congr v w (H0 : word_40 v = word_40 w) : port_11_4 v = port_11_4 w.
Proof. unfold port_11_4, closed_port_11_4. rewrite H0. reflexivity. Qed.
Lemma port_11_4_inputs v w (I0 : v 0 6 = w 0 6) : port_11_4 v = port_11_4 w.
Proof. apply port_11_4_congr.
 - apply word_40_inputs; assumption.
Qed.
