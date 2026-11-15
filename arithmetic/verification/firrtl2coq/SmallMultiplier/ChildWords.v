From Coq Require Import NArith ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From SmallMultiplier Require Import Child0Stable Child1Stable Child2Stable Compressors.
Local Open Scope N_scope.
Transparent Child0Stable.word_0 Child0Stable.word_1 Child0Stable.word_2 Child0Stable.word_3 Child0Stable.word_6 Child0Stable.word_7 Child0Stable.word_8 Child0Stable.word_9 Child0Stable.word_19 Child0Stable.word_20 Child0Stable.word_21 Child0Stable.word_22 Child0Stable.word_23 Child0Stable.word_24 Child0Stable.word_25 Child0Stable.word_4 Child0Stable.word_10 Child0Stable.word_26 Child0Stable.word_5 Child0Stable.word_11 Child0Stable.word_12 Child0Stable.word_13 Child0Stable.word_14 Child0Stable.word_15 Child0Stable.word_16 Child0Stable.word_17 Child0Stable.word_18.
Transparent Child1Stable.word_0 Child1Stable.word_1 Child1Stable.word_2 Child1Stable.word_3 Child1Stable.word_4 Child1Stable.word_7 Child1Stable.word_8 Child1Stable.word_9 Child1Stable.word_10 Child1Stable.word_11 Child1Stable.word_12 Child1Stable.word_13 Child1Stable.word_25 Child1Stable.word_23 Child1Stable.word_24 Child1Stable.word_26 Child1Stable.word_28 Child1Stable.word_27 Child1Stable.word_29 Child1Stable.word_30 Child1Stable.word_31 Child1Stable.word_32 Child1Stable.word_33 Child1Stable.word_5 Child1Stable.word_14 Child1Stable.word_34 Child1Stable.word_6 Child1Stable.word_15 Child1Stable.word_16 Child1Stable.word_17 Child1Stable.word_18 Child1Stable.word_19 Child1Stable.word_20 Child1Stable.word_21 Child1Stable.word_22.
Transparent Child2Stable.word_0 Child2Stable.word_1 Child2Stable.word_2 Child2Stable.word_3 Child2Stable.word_4 Child2Stable.word_5 Child2Stable.word_6 Child2Stable.port_10_5 Child2Stable.port_10_6 Child2Stable.port_11_5 Child2Stable.port_11_6 Child2Stable.word_12 Child2Stable.word_13 Child2Stable.word_14 Child2Stable.word_15 Child2Stable.word_16 Child2Stable.word_17 Child2Stable.word_18 Child2Stable.word_19 Child2Stable.word_20 Child2Stable.word_21 Child2Stable.word_22 Child2Stable.word_23 Child2Stable.word_24 Child2Stable.word_41 Child2Stable.word_7 Child2Stable.word_25 Child2Stable.word_42 Child2Stable.word_8 Child2Stable.word_26 Child2Stable.word_27 Child2Stable.word_43 Child2Stable.word_9 Child2Stable.word_28 Child2Stable.word_29 Child2Stable.word_30 Child2Stable.word_31 Child2Stable.word_32 Child2Stable.word_33 Child2Stable.word_34 Child2Stable.word_35 Child2Stable.word_36 Child2Stable.word_37 Child2Stable.word_38 Child2Stable.word_39 Child2Stable.word_40 Child2Stable.port_10_0 Child2Stable.port_10_1 Child2Stable.port_10_2 Child2Stable.port_10_3 Child2Stable.port_10_4 Child2Stable.port_11_0 Child2Stable.port_11_1 Child2Stable.port_11_2 Child2Stable.port_11_3 Child2Stable.port_11_4.
Definition c22_leaves (a b reset:bool) : Child0Stable.leaf_values :=
 fun scope id => [:: if scope == 0 then if id == 2 then a else if id == 3 then b else if id == 1 then reset else false else false].
Definition c32_leaves (a b c reset:bool) : Child1Stable.leaf_values :=
 fun scope id => [:: if scope == 0 then if id == 2 then a else if id == 3 then b else if id == 4 then c else if id == 1 then reset else false else false].
Definition c53_leaves (a b c d e reset:bool) : Child2Stable.leaf_values :=
 fun scope id => [:: if scope == 0 then if id == 2 then a else if id == 3 then b else if id == 4 then c else if id == 5 then d else if id == 6 then e else if id == 1 then reset else false
 else if scope == 10 then if id == 5 then fa_sum a b c else if id == 6 then fa_carry a b c else false
 else if scope == 11 then if id == 5 then fa_sum (fa_sum a b c) d e else if id == 6 then fa_carry (fa_sum a b c) d e else false else false].
Lemma child0_word4_bits a b reset : Child0Stable.word_4 (c22_leaves a b reset) = [::xorb a b].
Proof. destruct a,b,reset; vm_compute;reflexivity. Qed.
Lemma child0_word5_bits a b reset : Child0Stable.word_5 (c22_leaves a b reset) = [::andb a b].
Proof. destruct a,b,reset; vm_compute;reflexivity. Qed.
Lemma child0_assert_bits a b reset : Child0Stable.word_15 (c22_leaves a b reset) = [::true].
Proof. destruct a,b,reset; vm_compute;reflexivity. Qed.
Lemma child1_word5_bits a b c reset : Child1Stable.word_5 (c32_leaves a b c reset) = [::fa_sum a b c].
Proof. destruct a,b,c,reset; vm_compute;reflexivity. Qed.
Lemma child1_word6_bits a b c reset : Child1Stable.word_6 (c32_leaves a b c reset) = [::fa_carry a b c].
Proof. destruct a,b,c,reset; vm_compute;reflexivity. Qed.
Lemma child1_assert_bits a b c reset : Child1Stable.word_19 (c32_leaves a b c reset) = [::true].
Proof. destruct a,b,c,reset; vm_compute;reflexivity. Qed.
Lemma child2_word7_bits a b c d e reset : Child2Stable.word_7 (c53_leaves a b c d e reset) = [::fa_sum (fa_sum a b c) d e].
Proof. destruct a,b,c,d,e,reset; vm_compute;reflexivity. Qed.
Lemma child2_word8_bits a b c d e reset : Child2Stable.word_8 (c53_leaves a b c d e reset) = [::fa_carry a b c].
Proof. destruct a,b,c,d,e,reset; vm_compute;reflexivity. Qed.
Lemma child2_word9_bits a b c d e reset : Child2Stable.word_9 (c53_leaves a b c d e reset) = [::fa_carry (fa_sum a b c) d e].
Proof. destruct a,b,c,d,e,reset; vm_compute;reflexivity. Qed.
Lemma child2_assert_bits a b c d e reset : Child2Stable.word_34 (c53_leaves a b c d e reset) = [::true].
Proof. destruct a,b,c,d,e,reset; vm_compute;reflexivity. Qed.
Definition bool_Z (b:bool) : Z := if b then 1%Z else 0%Z.
Lemma child0_weight a b reset :
 (to_Zpos (Child0Stable.word_4 (c22_leaves a b reset)) +
 2 * to_Zpos (Child0Stable.word_5 (c22_leaves a b reset)))%Z =
 (bool_Z a + bool_Z b)%Z.
Proof. rewrite child0_word4_bits child0_word5_bits. destruct a,b; reflexivity. Qed.
Lemma child1_weight a b c reset :
 (to_Zpos (Child1Stable.word_5 (c32_leaves a b c reset)) +
 2 * to_Zpos (Child1Stable.word_6 (c32_leaves a b c reset)))%Z =
 (bool_Z a + bool_Z b +bool_Z c)%Z.
Proof. rewrite child1_word5_bits child1_word6_bits. destruct a,b,c; reflexivity. Qed.
Lemma child2_weight a b c d e reset :
 (to_Zpos (Child2Stable.word_7 (c53_leaves a b c d e reset)) +
 2 * to_Zpos (Child2Stable.word_8 (c53_leaves a b c d e reset)) +
 2 * to_Zpos (Child2Stable.word_9 (c53_leaves a b c d e reset)))%Z =
 (bool_Z a + bool_Z b +bool_Z c+bool_Z d+bool_Z e)%Z.
Proof. rewrite child2_word7_bits child2_word8_bits child2_word9_bits. destruct a,b,c,d,e; reflexivity. Qed.
Print Assumptions child2_weight.
