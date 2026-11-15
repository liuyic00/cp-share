From Coq Require Import NArith ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From SmallMultiplier Require Import Child0Stable Child1Stable Child2Stable Child0Congruence Child1Congruence Child2Congruence ChildWords Compressors.
Local Open Scope N_scope.
Lemma c22_generic_sum v a b (Ha:v 0 2=[::a]) (Hb:v 0 3=[::b]) :
 Child0Stable.word_4 v = [::xorb a b].
Proof. rewrite (Child0Congruence.word_4_inputs v (c22_leaves a b false) Ha Hb). apply child0_word4_bits. Qed.
Lemma c22_generic_carry v a b (Ha:v 0 2=[::a]) (Hb:v 0 3=[::b]) :
 Child0Stable.word_5 v = [::andb a b].
Proof. rewrite (Child0Congruence.word_5_inputs v (c22_leaves a b false) Ha Hb). apply child0_word5_bits. Qed.
Lemma c22_generic_assert v a b (Ha:v 0 2=[::a]) (Hb:v 0 3=[::b]) :
 Child0Stable.word_15 v = [::true].
Proof. rewrite (Child0Congruence.word_15_inputs v (c22_leaves a b false) Ha Hb). apply child0_assert_bits. Qed.
Lemma c32_generic_sum v a b c (Ha:v 0 2=[::a]) (Hb:v 0 3=[::b]) (Hc:v 0 4=[::c]) :
 Child1Stable.word_5 v = [::fa_sum a b c].
Proof. rewrite (Child1Congruence.word_5_inputs v (c32_leaves a b c false) Ha Hb Hc). apply child1_word5_bits. Qed.
Lemma c32_generic_carry v a b c (Ha:v 0 2=[::a]) (Hb:v 0 3=[::b]) (Hc:v 0 4=[::c]) :
 Child1Stable.word_6 v = [::fa_carry a b c].
Proof. rewrite (Child1Congruence.word_6_inputs v (c32_leaves a b c false) Ha Hb Hc). apply child1_word6_bits. Qed.
Lemma c32_generic_assert v a b c (Ha:v 0 2=[::a]) (Hb:v 0 3=[::b]) (Hc:v 0 4=[::c]) :
 Child1Stable.word_19 v = [::true].
Proof. rewrite (Child1Congruence.word_19_inputs v (c32_leaves a b c false) Ha Hb Hc). apply child1_assert_bits. Qed.
Transparent Child2Stable.word_7 Child2Stable.word_8 Child2Stable.word_9 Child2Stable.word_41 Child2Stable.word_42 Child2Stable.word_43 Child2Stable.port_10_6 Child2Stable.port_11_5 Child2Stable.port_11_6.
Lemma c53_generic_sum v : Child2Stable.word_7 v = v 11 5.
Proof. reflexivity. Qed.
Lemma c53_generic_carry0 v : Child2Stable.word_8 v = v 10 6.
Proof. reflexivity. Qed.
Lemma c53_generic_carry1 v : Child2Stable.word_9 v = v 11 6.
Proof. reflexivity. Qed.
