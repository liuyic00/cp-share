From Coq Require Import NArith ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From SmallMultiplier Require Import Child0Stable Child1Stable Child2Stable Child0Congruence Child1Congruence Child2Congruence ChildWords Compressors GlobalWidthFacts.
Local Open Scope N_scope.
Local Opaque Child0Stable.word_0 Child0Stable.word_1 Child0Stable.word_2 Child0Stable.word_3 Child0Stable.word_6 Child0Stable.word_7 Child0Stable.word_8 Child0Stable.word_9 Child0Stable.word_19 Child0Stable.word_20 Child0Stable.word_21 Child0Stable.word_22 Child0Stable.word_23 Child0Stable.word_24 Child0Stable.word_25 Child0Stable.word_4 Child0Stable.word_10 Child0Stable.word_26 Child0Stable.word_5 Child0Stable.word_11 Child0Stable.word_12 Child0Stable.word_13 Child0Stable.word_14 Child0Stable.word_15 Child0Stable.word_16 Child0Stable.word_17 Child0Stable.word_18.
Local Opaque Child1Stable.word_0 Child1Stable.word_1 Child1Stable.word_2 Child1Stable.word_3 Child1Stable.word_4 Child1Stable.word_7 Child1Stable.word_8 Child1Stable.word_9 Child1Stable.word_10 Child1Stable.word_11 Child1Stable.word_12 Child1Stable.word_13 Child1Stable.word_25 Child1Stable.word_23 Child1Stable.word_24 Child1Stable.word_26 Child1Stable.word_28 Child1Stable.word_27 Child1Stable.word_29 Child1Stable.word_30 Child1Stable.word_31 Child1Stable.word_32 Child1Stable.word_33 Child1Stable.word_5 Child1Stable.word_14 Child1Stable.word_34 Child1Stable.word_6 Child1Stable.word_15 Child1Stable.word_16 Child1Stable.word_17 Child1Stable.word_18 Child1Stable.word_19 Child1Stable.word_20 Child1Stable.word_21 Child1Stable.word_22.
Local Opaque Child2Stable.word_0 Child2Stable.word_1 Child2Stable.word_2 Child2Stable.word_3 Child2Stable.word_4 Child2Stable.word_5 Child2Stable.word_6 Child2Stable.port_10_5 Child2Stable.port_10_6 Child2Stable.port_11_5 Child2Stable.port_11_6 Child2Stable.word_12 Child2Stable.word_13 Child2Stable.word_14 Child2Stable.word_15 Child2Stable.word_16 Child2Stable.word_17 Child2Stable.word_18 Child2Stable.word_19 Child2Stable.word_20 Child2Stable.word_21 Child2Stable.word_22 Child2Stable.word_23 Child2Stable.word_24 Child2Stable.word_41 Child2Stable.word_7 Child2Stable.word_25 Child2Stable.word_42 Child2Stable.word_8 Child2Stable.word_26 Child2Stable.word_27 Child2Stable.word_43 Child2Stable.word_9 Child2Stable.word_28 Child2Stable.word_29 Child2Stable.word_30 Child2Stable.word_31 Child2Stable.word_32 Child2Stable.word_33 Child2Stable.word_34 Child2Stable.word_35 Child2Stable.word_36 Child2Stable.word_37 Child2Stable.word_38 Child2Stable.word_39 Child2Stable.word_40 Child2Stable.port_10_0 Child2Stable.port_10_1 Child2Stable.port_10_2 Child2Stable.port_10_3 Child2Stable.port_10_4 Child2Stable.port_11_0 Child2Stable.port_11_1 Child2Stable.port_11_2 Child2Stable.port_11_3 Child2Stable.port_11_4.
Lemma abstract_child0_4 (v:Child0Stable.leaf_values) (a b:bool)
 (E0_2:v 0 2 = [::a])
 (E0_3:v 0 3 = [::b])
 : Child0Stable.word_4 v = [::xorb a b].
Proof.
 transitivity (Child0Stable.word_4 (c22_leaves a b false)).
 - apply Child0Congruence.word_4_inputs.
   + exact E0_2.
   + exact E0_3.
 - apply child0_word4_bits.
Qed.
Lemma abstract_child0_5 (v:Child0Stable.leaf_values) (a b:bool)
 (E0_2:v 0 2 = [::a])
 (E0_3:v 0 3 = [::b])
 : Child0Stable.word_5 v = [::andb a b].
Proof.
 transitivity (Child0Stable.word_5 (c22_leaves a b false)).
 - apply Child0Congruence.word_5_inputs.
   + exact E0_2.
   + exact E0_3.
 - apply child0_word5_bits.
Qed.
Lemma abstract_child0_15 (v:Child0Stable.leaf_values) (a b:bool)
 (E0_2:v 0 2 = [::a])
 (E0_3:v 0 3 = [::b])
 : Child0Stable.word_15 v = [::true].
Proof.
 transitivity (Child0Stable.word_15 (c22_leaves a b false)).
 - apply Child0Congruence.word_15_inputs.
   + exact E0_2.
   + exact E0_3.
 - apply child0_assert_bits.
Qed.
Lemma abstract_child1_5 (v:Child1Stable.leaf_values) (a b c:bool)
 (E0_2:v 0 2 = [::a])
 (E0_3:v 0 3 = [::b])
 (E0_4:v 0 4 = [::c])
 : Child1Stable.word_5 v = [::fa_sum a b c].
Proof.
 transitivity (Child1Stable.word_5 (c32_leaves a b c false)).
 - apply Child1Congruence.word_5_inputs.
   + exact E0_2.
   + exact E0_3.
   + exact E0_4.
 - apply child1_word5_bits.
Qed.
Lemma abstract_child1_6 (v:Child1Stable.leaf_values) (a b c:bool)
 (E0_2:v 0 2 = [::a])
 (E0_3:v 0 3 = [::b])
 (E0_4:v 0 4 = [::c])
 : Child1Stable.word_6 v = [::fa_carry a b c].
Proof.
 transitivity (Child1Stable.word_6 (c32_leaves a b c false)).
 - apply Child1Congruence.word_6_inputs.
   + exact E0_2.
   + exact E0_3.
   + exact E0_4.
 - apply child1_word6_bits.
Qed.
Lemma abstract_child1_19 (v:Child1Stable.leaf_values) (a b c:bool)
 (E0_2:v 0 2 = [::a])
 (E0_3:v 0 3 = [::b])
 (E0_4:v 0 4 = [::c])
 : Child1Stable.word_19 v = [::true].
Proof.
 transitivity (Child1Stable.word_19 (c32_leaves a b c false)).
 - apply Child1Congruence.word_19_inputs.
   + exact E0_2.
   + exact E0_3.
   + exact E0_4.
 - apply child1_assert_bits.
Qed.
Lemma abstract_child2_7 (v:Child2Stable.leaf_values) (a b c d e:bool)
 (E11_5:v 11 5 = [::fa_sum (fa_sum a b c) d e])
 : Child2Stable.word_7 v = [::fa_sum (fa_sum a b c) d e].
Proof.
 transitivity (Child2Stable.word_7 (c53_leaves a b c d e false)).
 - apply Child2Congruence.word_7_inputs.
   + exact E11_5.
 - apply child2_word7_bits.
Qed.
Lemma abstract_child2_8 (v:Child2Stable.leaf_values) (a b c d e:bool)
 (E10_6:v 10 6 = [::fa_carry a b c])
 : Child2Stable.word_8 v = [::fa_carry a b c].
Proof.
 transitivity (Child2Stable.word_8 (c53_leaves a b c d e false)).
 - apply Child2Congruence.word_8_inputs.
   + exact E10_6.
 - apply child2_word8_bits.
Qed.
Lemma abstract_child2_9 (v:Child2Stable.leaf_values) (a b c d e:bool)
 (E11_6:v 11 6 = [::fa_carry (fa_sum a b c) d e])
 : Child2Stable.word_9 v = [::fa_carry (fa_sum a b c) d e].
Proof.
 transitivity (Child2Stable.word_9 (c53_leaves a b c d e false)).
 - apply Child2Congruence.word_9_inputs.
   + exact E11_6.
 - apply child2_word9_bits.
Qed.
Lemma abstract_child2_34 (v:Child2Stable.leaf_values) (a b c d e:bool)
 (E0_2:v 0 2 = [::a])
 (E0_3:v 0 3 = [::b])
 (E0_4:v 0 4 = [::c])
 (E0_5:v 0 5 = [::d])
 (E0_6:v 0 6 = [::e])
 (E10_6:v 10 6 = [::fa_carry a b c])
 (E11_5:v 11 5 = [::fa_sum (fa_sum a b c) d e])
 (E11_6:v 11 6 = [::fa_carry (fa_sum a b c) d e])
 : Child2Stable.word_34 v = [::true].
Proof.
 transitivity (Child2Stable.word_34 (c53_leaves a b c d e false)).
 - apply Child2Congruence.word_34_inputs.
   + exact E0_2.
   + exact E0_3.
   + exact E0_4.
   + exact E0_5.
   + exact E0_6.
   + exact E10_6.
   + exact E11_5.
   + exact E11_6.
 - apply child2_assert_bits.
Qed.
