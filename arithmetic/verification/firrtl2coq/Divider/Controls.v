From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From ArithmeticCommon Require Import BitvectorFacts NormalizationFacts.
From Divider Require Import Stable Representation Typing ReferenceNodes Slices Reductions Muxes MuxShapes Concats Log2 ScalarOps SliceOps LeafWords ControlStart Log2Bounds ControlSpecial ReferenceNormalization.
Local Open Scope Z_scope.
Lemma le_successor_lt z threshold : Z.leb (threshold + 1) z = Z.ltb threshold z.
Proof. destruct (Z.leb_spec0 (threshold + 1) z), (Z.ltb_spec0 threshold z); try reflexivity; lia. Qed.
Lemma normalized_eq_zero z : (if Z.eqb (normalize 1 z) 0 then 1 else 0) = Z.lxor (normalize 1 z) 1.
Proof.
 pose proof (normalize_range 1 z) as range. change (0 <= normalize 1 z < 2) in range.
 have cases : normalize 1 z = 0 \/ normalize 1 z = 1 by lia.
 destruct cases as [zero|one]; [rewrite zero|rewrite one]; reflexivity.
Qed.
Lemma known_bit_eq_zero z (fixed : normalize 1 z = z) : (if Z.eqb z 0 then 1 else 0) = Z.lxor z 1.
Proof. rewrite <- fixed. apply normalized_eq_zero. Qed.
Lemma normalize_zero width : normalize width 0 = 0.
Proof. apply Z.mod_0_l. pose proof (modulus_positive width). lia. Qed.

Lemma control_17_reference s i ghost : to_Zpos (word_17 (encoded_leaves s i ghost)) = Reference.v23 s i.
Proof.
 change (to_Zpos (word_17 (encoded_leaves s i ghost)) = (normalize 1 ((Z.lxor ((normalize 1 (if (negb (Z.eqb (normalize 64 (Reference.nio_5Fin_5Fbits_5Fsrc_5F1 i)) ((normalize 64 (0))))) then 1 else 0))) ((normalize 1 (1))))))).
 transitivity (normalize 1 (to_Zpos (word_17 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_17_size.
 -
 rewrite ?scalar_integer_17.
 rewrite ?(leaf_5_integer s i ghost).
 have literal_0 : to_Zpos [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false] = 0 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 1 1 = 1 by reflexivity.
 rewrite ?constant_0.
 have constant_1 : normalize 64 0 = 0 by reflexivity.
 rewrite ?constant_1.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_23_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_19_reference s i ghost : to_Zpos (word_19 (encoded_leaves s i ghost)) = Reference.v24 s i.
Proof.
 change (to_Zpos (word_19 (encoded_leaves s i ghost)) = (normalize 1 (if Z.eqb ((Reference.v2 s i)) 1 then ((Reference.v23 s i)) else (normalize 1 (Reference.r1_ndivBy0Reg s))))).
 transitivity (normalize 1 (to_Zpos (word_19 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_19_size.
 -
 rewrite ?mux_integer_19.
 rewrite ?(control_16_reference s i ghost).
 rewrite ?(control_17_reference s i ghost).
 rewrite ?(leaf_18_integer s i ghost).
 have literal_0 : to_Zpos [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false] = 0 by reflexivity.
 rewrite ?literal_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_2_widen; [|lia]).
 rewrite ?(known_bit_eq_zero _ (reference_2_normalized s i)).
 repeat (rewrite reference_23_widen; [|lia]).
 rewrite ?(known_bit_eq_zero _ (reference_23_normalized s i)).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_24_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_24_reference s i ghost : to_Zpos (word_24 (encoded_leaves s i ghost)) = Reference.v46 s i.
Proof.
 change (to_Zpos (word_24 (encoded_leaves s i ghost)) = (normalize 1 ((Z.land ((Reference.v45 s i)) (normalize 1 (Reference.nctrl_5Fsign i)))))).
 transitivity (normalize 1 (to_Zpos (word_24 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_24_size.
 -
 rewrite ?scalar_integer_24.
 rewrite ?(leaf_10_integer s i ghost).
 rewrite ?(slice_23_reference s i ghost).
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_45_widen; [|lia]).
 rewrite ?(known_bit_eq_zero _ (reference_45_normalized s i)).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_46_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_26_reference s i ghost : to_Zpos (word_26 (encoded_leaves s i ghost)) = Reference.v56 s i.
Proof.
 change (to_Zpos (word_26 (encoded_leaves s i ghost)) = (normalize 64 ((Z.sub ((normalize 64 (0))) (normalize 64 (Reference.nio_5Fin_5Fbits_5Fsrc_5F0 i)))))).
 transitivity (normalize 64 (to_Zpos (word_26 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_26_size.
 -
 rewrite ?slice_integer_26.
 rewrite ?scalar_integer_25.
 rewrite ?(leaf_4_integer s i ghost).
 have literal_0 : to_Zpos [::false] = 0 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 64 0 = 0 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_56_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 64)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_27_reference s i ghost : to_Zpos (word_27 (encoded_leaves s i ghost)) = Reference.v57 s i.
Proof.
 change (to_Zpos (word_27 (encoded_leaves s i ghost)) = (normalize 64 (if Z.eqb ((Reference.v46 s i)) 1 then ((Reference.v56 s i)) else (normalize 64 (Reference.nio_5Fin_5Fbits_5Fsrc_5F0 i))))).
 transitivity (normalize 64 (to_Zpos (word_27 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_27_size.
 -
 rewrite ?mux_integer_27.
 rewrite ?(leaf_4_integer s i ghost).
 rewrite ?(control_24_reference s i ghost).
 rewrite ?(control_26_reference s i ghost).
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_46_widen; [|lia]).
 rewrite ?(known_bit_eq_zero _ (reference_46_normalized s i)).
 repeat (rewrite reference_56_widen; [|lia]).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_57_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 64)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_29_reference s i ghost : to_Zpos (word_29 (encoded_leaves s i ghost)) = Reference.v49 s i.
Proof.
 change (to_Zpos (word_29 (encoded_leaves s i ghost)) = (normalize 1 ((Z.land ((Reference.v48 s i)) (normalize 1 (Reference.nctrl_5Fsign i)))))).
 transitivity (normalize 1 (to_Zpos (word_29 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_29_size.
 -
 rewrite ?scalar_integer_29.
 rewrite ?(leaf_10_integer s i ghost).
 rewrite ?(slice_28_reference s i ghost).
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_48_widen; [|lia]).
 rewrite ?(known_bit_eq_zero _ (reference_48_normalized s i)).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_49_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_31_reference s i ghost : to_Zpos (word_31 (encoded_leaves s i ghost)) = Reference.v53 s i.
Proof.
 change (to_Zpos (word_31 (encoded_leaves s i ghost)) = (normalize 64 ((Z.sub ((normalize 64 (0))) (normalize 64 (Reference.nio_5Fin_5Fbits_5Fsrc_5F1 i)))))).
 transitivity (normalize 64 (to_Zpos (word_31 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_31_size.
 -
 rewrite ?slice_integer_31.
 rewrite ?scalar_integer_30.
 rewrite ?(leaf_5_integer s i ghost).
 have literal_0 : to_Zpos [::false] = 0 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 64 0 = 0 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_53_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 64)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_32_reference s i ghost : to_Zpos (word_32 (encoded_leaves s i ghost)) = Reference.v54 s i.
Proof.
 change (to_Zpos (word_32 (encoded_leaves s i ghost)) = (normalize 64 (if Z.eqb ((Reference.v49 s i)) 1 then ((Reference.v53 s i)) else (normalize 64 (Reference.nio_5Fin_5Fbits_5Fsrc_5F1 i))))).
 transitivity (normalize 64 (to_Zpos (word_32 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_32_size.
 -
 rewrite ?mux_integer_32.
 rewrite ?(leaf_5_integer s i ghost).
 rewrite ?(control_29_reference s i ghost).
 rewrite ?(control_31_reference s i ghost).
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_49_widen; [|lia]).
 rewrite ?(known_bit_eq_zero _ (reference_49_normalized s i)).
 repeat (rewrite reference_53_widen; [|lia]).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_54_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 64)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_34_reference s i ghost : to_Zpos (word_34 (encoded_leaves s i ghost)) = Reference.v47 s i.
Proof.
 change (to_Zpos (word_34 (encoded_leaves s i ghost)) = (normalize 1 (if Z.eqb ((Reference.v2 s i)) 1 then ((Reference.v46 s i)) else (normalize 1 (Reference.r3_naSignReg s))))).
 transitivity (normalize 1 (to_Zpos (word_34 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_34_size.
 -
 rewrite ?mux_integer_34.
 rewrite ?(control_16_reference s i ghost).
 rewrite ?(control_24_reference s i ghost).
 rewrite ?(leaf_33_integer s i ghost).
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_2_widen; [|lia]).
 rewrite ?(known_bit_eq_zero _ (reference_2_normalized s i)).
 repeat (rewrite reference_46_widen; [|lia]).
 rewrite ?(known_bit_eq_zero _ (reference_46_normalized s i)).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_47_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_35_reference s i ghost : to_Zpos (word_35 (encoded_leaves s i ghost)) = Reference.v50 s i.
Proof.
 change (to_Zpos (word_35 (encoded_leaves s i ghost)) = (normalize 1 ((Z.lxor ((Reference.v46 s i)) ((Reference.v49 s i)))))).
 transitivity (normalize 1 (to_Zpos (word_35 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_35_size.
 -
 rewrite ?scalar_integer_35.
 rewrite ?(control_24_reference s i ghost).
 rewrite ?(control_29_reference s i ghost).
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_46_widen; [|lia]).
 rewrite ?(known_bit_eq_zero _ (reference_46_normalized s i)).
 repeat (rewrite reference_49_widen; [|lia]).
 rewrite ?(known_bit_eq_zero _ (reference_49_normalized s i)).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_50_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_37_reference s i ghost : to_Zpos (word_37 (encoded_leaves s i ghost)) = Reference.v51 s i.
Proof.
 change (to_Zpos (word_37 (encoded_leaves s i ghost)) = (normalize 1 ((Z.land ((Reference.v50 s i)) ((Reference.v21 s i)))))).
 transitivity (normalize 1 (to_Zpos (word_37 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_37_size.
 -
 rewrite ?scalar_integer_37.
 rewrite ?(control_35_reference s i ghost).
 rewrite ?(control_36_reference s i ghost).
 have literal_0 : to_Zpos [::false] = 0 by reflexivity.
 rewrite ?literal_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_21_widen; [|lia]).
 rewrite ?(known_bit_eq_zero _ (reference_21_normalized s i)).
 repeat (rewrite reference_50_widen; [|lia]).
 rewrite ?(known_bit_eq_zero _ (reference_50_normalized s i)).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_51_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_39_reference s i ghost : to_Zpos (word_39 (encoded_leaves s i ghost)) = Reference.v52 s i.
Proof.
 change (to_Zpos (word_39 (encoded_leaves s i ghost)) = (normalize 1 (if Z.eqb ((Reference.v2 s i)) 1 then ((Reference.v51 s i)) else (normalize 1 (Reference.r4_nqSignReg s))))).
 transitivity (normalize 1 (to_Zpos (word_39 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_39_size.
 -
 rewrite ?mux_integer_39.
 rewrite ?(control_16_reference s i ghost).
 rewrite ?(control_37_reference s i ghost).
 rewrite ?(leaf_38_integer s i ghost).
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_2_widen; [|lia]).
 rewrite ?(known_bit_eq_zero _ (reference_2_normalized s i)).
 repeat (rewrite reference_51_widen; [|lia]).
 rewrite ?(known_bit_eq_zero _ (reference_51_normalized s i)).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_52_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_41_reference s i ghost : to_Zpos (word_41 (encoded_leaves s i ghost)) = Reference.v55 s i.
Proof.
 change (to_Zpos (word_41 (encoded_leaves s i ghost)) = (normalize 64 (if Z.eqb ((Reference.v2 s i)) 1 then ((Reference.v54 s i)) else (normalize 64 (Reference.r5_nbReg s))))).
 transitivity (normalize 64 (to_Zpos (word_41 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_41_size.
 -
 rewrite ?mux_integer_41.
 rewrite ?(control_16_reference s i ghost).
 rewrite ?(control_32_reference s i ghost).
 rewrite ?(leaf_40_integer s i ghost).
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_2_widen; [|lia]).
 rewrite ?(known_bit_eq_zero _ (reference_2_normalized s i)).
 repeat (rewrite reference_54_widen; [|lia]).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_55_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 64)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_42_reference s i ghost : to_Zpos (word_42 (encoded_leaves s i ghost)) = Reference.v58 s i.
Proof.
 change (to_Zpos (word_42 (encoded_leaves s i ghost)) = (normalize 65 ((Z.shiftl (((Reference.v57 s i))) 1 + ((normalize 1 (0))))))).
 transitivity (normalize 65 (to_Zpos (word_42 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_42_size.
 -
 rewrite ?concat_integer_42.
 rewrite ?(control_27_reference s i ghost).
 have literal_0 : to_Zpos [::false] = 0 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 1 0 = 0 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_57_widen; [|lia]).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_58_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 65)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_44_reference s i ghost : to_Zpos (word_44 (encoded_leaves s i ghost)) = Reference.v59 s i.
Proof.
 change (to_Zpos (word_44 (encoded_leaves s i ghost)) = (normalize 65 (if Z.eqb ((Reference.v2 s i)) 1 then ((Reference.v58 s i)) else (normalize 65 (Reference.r6_naValx2Reg s))))).
 transitivity (normalize 65 (to_Zpos (word_44 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_44_size.
 -
 rewrite ?mux_integer_44.
 rewrite ?(control_16_reference s i ghost).
 rewrite ?(control_42_reference s i ghost).
 rewrite ?(leaf_43_integer s i ghost).
 have literal_0 : to_Zpos [::false] = 0 by reflexivity.
 rewrite ?literal_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_2_widen; [|lia]).
 rewrite ?(known_bit_eq_zero _ (reference_2_normalized s i)).
 repeat (rewrite reference_58_widen; [|lia]).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_59_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 65)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_48_reference s i ghost : to_Zpos (word_48 (encoded_leaves s i ghost)) = Reference.v61 s i.
Proof.
 change (to_Zpos (word_48 (encoded_leaves s i ghost)) = (normalize 1 (if Z.eqb ((Reference.v2 s i)) 1 then (normalize 1 (Reference.nctrl_5FisHi i)) else (normalize 1 (Reference.r8_nctrlReg_5FisHi s))))).
 transitivity (normalize 1 (to_Zpos (word_48 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_48_size.
 -
 rewrite ?mux_integer_48.
 rewrite ?(leaf_12_integer s i ghost).
 rewrite ?(control_16_reference s i ghost).
 rewrite ?(leaf_47_integer s i ghost).
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_2_widen; [|lia]).
 rewrite ?(known_bit_eq_zero _ (reference_2_normalized s i)).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_61_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_49_reference s i ghost : to_Zpos (word_49 (encoded_leaves s i ghost)) = Reference.v60 s i.
Proof.
 change (to_Zpos (word_49 (encoded_leaves s i ghost)) = (normalize 1 (if Z.eqb ((Reference.v2 s i)) 1 then (normalize 1 (Reference.nctrl_5FisW i)) else (normalize 1 (Reference.r7_nctrlReg_5FisW s))))).
 transitivity (normalize 1 (to_Zpos (word_49 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_49_size.
 -
 rewrite ?mux_integer_49.
 rewrite ?(leaf_11_integer s i ghost).
 rewrite ?(control_16_reference s i ghost).
 rewrite ?(leaf_46_integer s i ghost).
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_2_widen; [|lia]).
 rewrite ?(known_bit_eq_zero _ (reference_2_normalized s i)).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_60_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_52_reference s i ghost : to_Zpos (word_52 (encoded_leaves s i ghost)) = Reference.v4 s i.
Proof.
 change (to_Zpos (word_52 (encoded_leaves s i ghost)) = (normalize 1 (if (Z.eqb (normalize 3 (Reference.r0_nstate s)) ((normalize 3 (1)))) then 1 else 0))).
 transitivity (normalize 1 (to_Zpos (word_52 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_52_size.
 -
 rewrite ?scalar_integer_52.
 rewrite ?(leaf_13_integer s i ghost).
 have literal_0 : to_Zpos [::true; false; false] = 1 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 3 1 = 1 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_4_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_209_reference s i ghost : to_Zpos (word_209 (encoded_leaves s i ghost)) = Reference.v226 s i.
Proof.
 change (to_Zpos (word_209 (encoded_leaves s i ghost)) = (Reference.v226 s i)).
 transitivity (normalize 7 (to_Zpos (word_209 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_209_size.
 -
 rewrite ?slice_integer_209.
 rewrite ?(log2_208_reference s i ghost).
 have literal_0 : to_Zpos [::false; false; false; false; false; false; true] = 64 by reflexivity.
 rewrite ?literal_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_226_widen; [|lia]).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_226_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 7)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_371_reference s i ghost : to_Zpos (word_371 (encoded_leaves s i ghost)) = Reference.v386 s i.
Proof.
 change (to_Zpos (word_371 (encoded_leaves s i ghost)) = (normalize 7 ((Z.sub ((Reference.v226 s i)) ((Reference.v385 s i)))))).
 transitivity (normalize 7 (to_Zpos (word_371 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_371_size.
 -
 rewrite ?slice_integer_371.
 rewrite ?scalar_integer_370.
 rewrite ?(control_209_reference s i ghost).
 rewrite ?(log2_369_reference s i ghost).
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_226_widen; [|lia]).
 repeat (rewrite reference_385_widen; [|lia]).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_386_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 7)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_372_reference s i ghost : to_Zpos (word_372 (encoded_leaves s i ghost)) = Reference.v388 s i.
Proof.
 change (to_Zpos (word_372 (encoded_leaves s i ghost)) = (normalize 1 (if (Z.ltb ((normalize 7 (62))) ((Reference.v386 s i))) then 1 else 0))).
 transitivity (normalize 1 (to_Zpos (word_372 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_372_size.
 -
 rewrite ?scalar_integer_372.
 rewrite ?(control_371_reference s i ghost).
 have literal_0 : to_Zpos [::true; true; true; true; true; true] = 63 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 7 62 = 62 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_386_widen; [|lia]).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_388_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_375_reference s i ghost : to_Zpos (word_375 (encoded_leaves s i ghost)) = Reference.v6 s i.
Proof.
 change (to_Zpos (word_375 (encoded_leaves s i ghost)) = (normalize 1 (if (Z.eqb (normalize 3 (Reference.r0_nstate s)) ((normalize 3 (2)))) then 1 else 0))).
 transitivity (normalize 1 (to_Zpos (word_375 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_375_size.
 -
 rewrite ?scalar_integer_375.
 rewrite ?(leaf_13_integer s i ghost).
 have literal_0 : to_Zpos [::false; true; false] = 2 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 3 2 = 2 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_6_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_376_reference s i ghost : to_Zpos (word_376 (encoded_leaves s i ghost)) = Reference.v31 s i.
Proof.
 change (to_Zpos (word_376 (encoded_leaves s i ghost)) = (normalize 128 (Z.shiftl ((normalize 128 ((Z.shiftl (((normalize 63 (0)))) 65 + (normalize 65 (Reference.r6_naValx2Reg s)))))) ((normalize 128 ((Z.shiftl (((normalize 122 (0)))) 6 + (normalize 6 (Reference.r9_ncnt_5Fvalue s))))))))).
 transitivity (normalize 128 (to_Zpos (word_376 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_376_size.
 -
 rewrite ?shift_376_integer.
 rewrite ?(leaf_43_integer s i ghost).
 rewrite ?(leaf_51_integer s i ghost).
 have constant_0 : normalize 122 0 = 0 by reflexivity.
 rewrite ?constant_0.
 have constant_1 : normalize 63 0 = 0 by reflexivity.
 rewrite ?constant_1.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_31_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 128)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_377_reference s i ghost : to_Zpos (word_377 (encoded_leaves s i ghost)) = Reference.v8 s i.
Proof.
 change (to_Zpos (word_377 (encoded_leaves s i ghost)) = (normalize 1 (if (Z.eqb (normalize 3 (Reference.r0_nstate s)) ((normalize 3 (3)))) then 1 else 0))).
 transitivity (normalize 1 (to_Zpos (word_377 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_377_size.
 -
 rewrite ?scalar_integer_377.
 rewrite ?(leaf_13_integer s i ghost).
 have literal_0 : to_Zpos [::true; true; false] = 3 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 3 3 = 3 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_8_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_378_reference s i ghost : to_Zpos (word_378 (encoded_leaves s i ghost)) = Reference.v35 s i.
Proof.
 change (to_Zpos (word_378 (encoded_leaves s i ghost)) = (normalize 1 (if (Z.leb ((normalize 65 ((Z.shiftl (((normalize 1 (0)))) 64 + (normalize 64 (Reference.r5_nbReg s)))))) ((Reference.v33 s i))) then 1 else 0))).
 transitivity (normalize 1 (to_Zpos (word_378 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_378_size.
 -
 rewrite ?scalar_integer_378.
 rewrite ?(slice_21_reference s i ghost).
 rewrite ?(leaf_40_integer s i ghost).
 have constant_0 : normalize 1 0 = 0 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_33_widen; [|lia]).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_35_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_385_reference s i ghost : to_Zpos (word_385 (encoded_leaves s i ghost)) = Reference.v10 s i.
Proof.
 change (to_Zpos (word_385 (encoded_leaves s i ghost)) = (normalize 1 (if (Z.eqb (normalize 6 (Reference.r9_ncnt_5Fvalue s)) ((normalize 6 (63)))) then 1 else 0))).
 transitivity (normalize 1 (to_Zpos (word_385 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_385_size.
 -
 rewrite ?scalar_integer_385.
 rewrite ?(leaf_51_integer s i ghost).
 have literal_0 : to_Zpos [::true; true; true; true; true; true] = 63 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 6 63 = 63 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_10_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_387_reference s i ghost : to_Zpos (word_387 (encoded_leaves s i ghost)) = Reference.v395 s i.
Proof.
 change (to_Zpos (word_387 (encoded_leaves s i ghost)) = (normalize 6 ((Z.add (normalize 6 (Reference.r9_ncnt_5Fvalue s)) ((normalize 6 (1))))))).
 transitivity (normalize 6 (to_Zpos (word_387 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_387_size.
 -
 rewrite ?slice_integer_387.
 rewrite ?scalar_integer_386.
 rewrite ?(leaf_51_integer s i ghost).
 have literal_0 : to_Zpos [::true] = 1 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 6 1 = 1 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_395_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 6)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_388_reference s i ghost : to_Zpos (word_388 (encoded_leaves s i ghost)) = Reference.v10 s i.
Proof.
 change (to_Zpos (word_388 (encoded_leaves s i ghost)) = (normalize 1 (if (Z.eqb (normalize 6 (Reference.r9_ncnt_5Fvalue s)) ((normalize 6 (63)))) then 1 else 0))).
 transitivity (normalize 1 (to_Zpos (word_388 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_388_size.
 -
 rewrite ?scalar_integer_388.
 rewrite ?(leaf_51_integer s i ghost).
 have literal_0 : to_Zpos [::true; true; true; true; true; true] = 63 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 6 63 = 63 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_10_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_389_reference s i ghost : to_Zpos (word_389 (encoded_leaves s i ghost)) = Reference.v12 s i.
Proof.
 change (to_Zpos (word_389 (encoded_leaves s i ghost)) = (normalize 3 (if Z.eqb ((Reference.v10 s i)) 1 then ((normalize 3 (4))) else (normalize 3 (Reference.r0_nstate s))))).
 transitivity (normalize 3 (to_Zpos (word_389 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_389_size.
 -
 rewrite ?mux_integer_389.
 rewrite ?(leaf_13_integer s i ghost).
 rewrite ?(control_388_reference s i ghost).
 have literal_0 : to_Zpos [::false; false; true] = 4 by reflexivity.
 rewrite ?literal_0.
 have literal_1 : to_Zpos [::true; true; true; true; true; true] = 63 by reflexivity.
 rewrite ?literal_1.
 have constant_0 : normalize 3 4 = 4 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_10_widen; [|lia]).
 rewrite ?(known_bit_eq_zero _ (reference_10_normalized s i)).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_12_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 3)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_390_reference s i ghost : to_Zpos (word_390 (encoded_leaves s i ghost)) = Reference.v13 s i.
Proof.
 change (to_Zpos (word_390 (encoded_leaves s i ghost)) = (normalize 1 (if (Z.eqb (normalize 3 (Reference.r0_nstate s)) ((normalize 3 (4)))) then 1 else 0))).
 transitivity (normalize 1 (to_Zpos (word_390 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_390_size.
 -
 rewrite ?scalar_integer_390.
 rewrite ?(leaf_13_integer s i ghost).
 have literal_0 : to_Zpos [::false; false; true] = 4 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 3 4 = 4 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_13_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_407_reference s i ghost : to_Zpos (word_407 (encoded_leaves s i ghost)) = Reference.v405 s i.
Proof.
 change (to_Zpos (word_407 (encoded_leaves s i ghost)) = (normalize 64 ((Z.sub ((normalize 64 (0))) ((Reference.v40 s i)))))).
 transitivity (normalize 64 (to_Zpos (word_407 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_407_size.
 -
 rewrite ?slice_integer_407.
 rewrite ?scalar_integer_406.
 rewrite ?(slice_22_reference s i ghost).
 have literal_0 : to_Zpos [::false] = 0 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 64 0 = 0 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_40_widen; [|lia]).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_405_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 64)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_408_reference s i ghost : to_Zpos (word_408 (encoded_leaves s i ghost)) = Reference.v406 s i.
Proof.
 change (to_Zpos (word_408 (encoded_leaves s i ghost)) = (normalize 64 (if Z.eqb (normalize 1 (Reference.r4_nqSignReg s)) 1 then ((Reference.v405 s i)) else ((Reference.v40 s i))))).
 transitivity (normalize 64 (to_Zpos (word_408 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_408_size.
 -
 rewrite ?mux_integer_408.
 rewrite ?(slice_22_reference s i ghost).
 rewrite ?(leaf_38_integer s i ghost).
 rewrite ?(control_407_reference s i ghost).
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_40_widen; [|lia]).
 repeat (rewrite reference_405_widen; [|lia]).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_406_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 64)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_410_reference s i ghost : to_Zpos (word_410 (encoded_leaves s i ghost)) = Reference.v403 s i.
Proof.
 change (to_Zpos (word_410 (encoded_leaves s i ghost)) = (normalize 64 ((Z.sub ((normalize 64 (0))) ((Reference.v402 s i)))))).
 transitivity (normalize 64 (to_Zpos (word_410 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_410_size.
 -
 rewrite ?slice_integer_410.
 rewrite ?scalar_integer_409.
 rewrite ?(control_405_reference s i ghost).
 have literal_0 : to_Zpos [::false] = 0 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 64 0 = 0 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_402_widen; [|lia]).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_403_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 64)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_411_reference s i ghost : to_Zpos (word_411 (encoded_leaves s i ghost)) = Reference.v404 s i.
Proof.
 change (to_Zpos (word_411 (encoded_leaves s i ghost)) = (normalize 64 (if Z.eqb (normalize 1 (Reference.r3_naSignReg s)) 1 then ((Reference.v403 s i)) else ((Reference.v402 s i))))).
 transitivity (normalize 64 (to_Zpos (word_411 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_411_size.
 -
 rewrite ?mux_integer_411.
 rewrite ?(leaf_33_integer s i ghost).
 rewrite ?(control_405_reference s i ghost).
 rewrite ?(control_410_reference s i ghost).
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_402_widen; [|lia]).
 repeat (rewrite reference_403_widen; [|lia]).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_404_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 64)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_412_reference s i ghost : to_Zpos (word_412 (encoded_leaves s i ghost)) = Reference.v407 s i.
Proof.
 change (to_Zpos (word_412 (encoded_leaves s i ghost)) = (normalize 64 (if Z.eqb (normalize 1 (Reference.r8_nctrlReg_5FisHi s)) 1 then ((Reference.v404 s i)) else ((Reference.v406 s i))))).
 transitivity (normalize 64 (to_Zpos (word_412 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_412_size.
 -
 rewrite ?mux_integer_412.
 rewrite ?(leaf_47_integer s i ghost).
 rewrite ?(control_408_reference s i ghost).
 rewrite ?(control_411_reference s i ghost).
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_404_widen; [|lia]).
 repeat (rewrite reference_406_widen; [|lia]).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_407_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 64)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_419_reference s i ghost : to_Zpos (word_419 (encoded_leaves s i ghost)) = Reference.v13 s i.
Proof.
 change (to_Zpos (word_419 (encoded_leaves s i ghost)) = (normalize 1 (if (Z.eqb (normalize 3 (Reference.r0_nstate s)) ((normalize 3 (4)))) then 1 else 0))).
 transitivity (normalize 1 (to_Zpos (word_419 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_419_size.
 -
 rewrite ?scalar_integer_419.
 rewrite ?(leaf_13_integer s i ghost).
 have literal_0 : to_Zpos [::false; false; true] = 4 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 3 4 = 4 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_13_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_421_reference s i ghost : to_Zpos (word_421 (encoded_leaves s i ghost)) = Reference.v414 s i.
Proof.
 change (to_Zpos (word_421 (encoded_leaves s i ghost)) = (normalize 1 (if (Z.eqb ((Reference.v40 s i)) ((normalize 64 (18446744073709551615)))) then 1 else 0))).
 transitivity (normalize 1 (to_Zpos (word_421 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_421_size.
 -
 rewrite ?scalar_integer_421.
 rewrite ?(slice_22_reference s i ghost).
 have literal_0 : to_Zpos [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true] = 18446744073709551615 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 64 18446744073709551615 = 18446744073709551615 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_40_widen; [|lia]).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_414_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_423_reference s i ghost : to_Zpos (word_423 (encoded_leaves s i ghost)) = Reference.v415 s i.
Proof.
 change (to_Zpos (word_423 (encoded_leaves s i ghost)) = (normalize 1 ((Z.lxor (normalize 1 (Reference.nreset i)) ((normalize 1 (1))))))).
 transitivity (normalize 1 (to_Zpos (word_423 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_423_size.
 -
 rewrite ?scalar_integer_423.
 rewrite ?slice_integer_422.
 rewrite ?(leaf_1_integer s i ghost).
 have literal_0 : to_Zpos [::false] = 0 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 1 1 = 1 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_415_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_426_reference s i ghost : to_Zpos (word_426 (encoded_leaves s i ghost)) = Reference.v418 s i.
Proof.
 change (to_Zpos (word_426 (encoded_leaves s i ghost)) = (normalize 1 (if (Z.eqb ((Reference.v402 s i)) ((Reference.v417 s i))) then 1 else 0))).
 transitivity (normalize 1 (to_Zpos (word_426 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_426_size.
 -
 rewrite ?scalar_integer_426.
 rewrite ?(control_405_reference s i ghost).
 rewrite ?(control_425_reference s i ghost).
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_402_widen; [|lia]).
 repeat (rewrite reference_417_widen; [|lia]).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_418_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_428_reference s i ghost : to_Zpos (word_428 (encoded_leaves s i ghost)) = Reference.v415 s i.
Proof.
 change (to_Zpos (word_428 (encoded_leaves s i ghost)) = (normalize 1 ((Z.lxor (normalize 1 (Reference.nreset i)) ((normalize 1 (1))))))).
 transitivity (normalize 1 (to_Zpos (word_428 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_428_size.
 -
 rewrite ?scalar_integer_428.
 rewrite ?slice_integer_427.
 rewrite ?(leaf_1_integer s i ghost).
 have literal_0 : to_Zpos [::false] = 0 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 1 1 = 1 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_415_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_430_reference s i ghost : to_Zpos (word_430 (encoded_leaves s i ghost)) = Reference.v419 s i.
Proof.
 change (to_Zpos (word_430 (encoded_leaves s i ghost)) = (normalize 1 (if (negb (Z.eqb (normalize 64 (Reference.r5_nbReg s)) ((normalize 64 (0))))) then 1 else 0))).
 transitivity (normalize 1 (to_Zpos (word_430 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_430_size.
 -
 rewrite ?scalar_integer_430.
 rewrite ?(leaf_40_integer s i ghost).
 have literal_0 : to_Zpos [::false] = 0 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 64 0 = 0 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_419_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_432_reference s i ghost : to_Zpos (word_432 (encoded_leaves s i ghost)) = Reference.v415 s i.
Proof.
 change (to_Zpos (word_432 (encoded_leaves s i ghost)) = (normalize 1 ((Z.lxor (normalize 1 (Reference.nreset i)) ((normalize 1 (1))))))).
 transitivity (normalize 1 (to_Zpos (word_432 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_432_size.
 -
 rewrite ?scalar_integer_432.
 rewrite ?slice_integer_431.
 rewrite ?(leaf_1_integer s i ghost).
 have literal_0 : to_Zpos [::false] = 0 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 1 1 = 1 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_415_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_434_reference s i ghost : to_Zpos (word_434 (encoded_leaves s i ghost)) = Reference.v424 s i.
Proof.
 change (to_Zpos (word_434 (encoded_leaves s i ghost)) = (normalize 128 ((Z.mul ((normalize 128 ((Z.shiftl (((normalize 64 (0)))) 64 + ((Reference.v40 s i)))))) ((normalize 128 ((Z.shiftl (((normalize 64 (0)))) 64 + (normalize 64 (Reference.r5_nbReg s)))))))))).
 transitivity (normalize 128 (to_Zpos (word_434 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_434_size.
 -
 rewrite ?scalar_integer_434.
 rewrite ?(slice_22_reference s i ghost).
 rewrite ?(leaf_40_integer s i ghost).
 have constant_0 : normalize 64 0 = 0 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_40_widen; [|lia]).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_424_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 128)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_435_reference s i ghost : to_Zpos (word_435 (encoded_leaves s i ghost)) = Reference.v428 s i.
Proof.
 change (to_Zpos (word_435 (encoded_leaves s i ghost)) = (normalize 129 ((Z.add ((normalize 129 ((Z.shiftl (((normalize 1 (0)))) 128 + ((Reference.v424 s i)))))) ((normalize 129 ((Z.shiftl (((normalize 65 (0)))) 64 + ((Reference.v402 s i)))))))))).
 transitivity (normalize 129 (to_Zpos (word_435 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_435_size.
 -
 rewrite ?scalar_integer_435.
 rewrite ?(control_405_reference s i ghost).
 rewrite ?(control_434_reference s i ghost).
 have constant_0 : normalize 1 0 = 0 by reflexivity.
 rewrite ?constant_0.
 have constant_1 : normalize 65 0 = 0 by reflexivity.
 rewrite ?constant_1.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_402_widen; [|lia]).
 repeat (rewrite reference_424_widen; [|lia]).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_428_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 129)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_437_reference s i ghost : to_Zpos (word_437 (encoded_leaves s i ghost)) = Reference.v430 s i.
Proof.
 change (to_Zpos (word_437 (encoded_leaves s i ghost)) = (normalize 1 (if (Z.eqb ((Reference.v428 s i)) ((normalize 129 ((Z.shiftl (((normalize 65 (0)))) 64 + ((Reference.v417 s i))))))) then 1 else 0))).
 transitivity (normalize 1 (to_Zpos (word_437 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_437_size.
 -
 rewrite ?scalar_integer_437.
 rewrite ?(control_435_reference s i ghost).
 rewrite ?(control_436_reference s i ghost).
 have constant_0 : normalize 65 0 = 0 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_417_widen; [|lia]).
 repeat (rewrite reference_428_widen; [|lia]).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_430_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_439_reference s i ghost : to_Zpos (word_439 (encoded_leaves s i ghost)) = Reference.v415 s i.
Proof.
 change (to_Zpos (word_439 (encoded_leaves s i ghost)) = (normalize 1 ((Z.lxor (normalize 1 (Reference.nreset i)) ((normalize 1 (1))))))).
 transitivity (normalize 1 (to_Zpos (word_439 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_439_size.
 -
 rewrite ?scalar_integer_439.
 rewrite ?slice_integer_438.
 rewrite ?(leaf_1_integer s i ghost).
 have literal_0 : to_Zpos [::false] = 0 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 1 1 = 1 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_415_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_441_reference s i ghost : to_Zpos (word_441 (encoded_leaves s i ghost)) = Reference.v431 s i.
Proof.
 change (to_Zpos (word_441 (encoded_leaves s i ghost)) = (normalize 1 (if (Z.ltb ((Reference.v402 s i)) (normalize 64 (Reference.r5_nbReg s))) then 1 else 0))).
 transitivity (normalize 1 (to_Zpos (word_441 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_441_size.
 -
 rewrite ?scalar_integer_441.
 rewrite ?(leaf_40_integer s i ghost).
 rewrite ?(control_405_reference s i ghost).
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_402_widen; [|lia]).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_431_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_443_reference s i ghost : to_Zpos (word_443 (encoded_leaves s i ghost)) = Reference.v415 s i.
Proof.
 change (to_Zpos (word_443 (encoded_leaves s i ghost)) = (normalize 1 ((Z.lxor (normalize 1 (Reference.nreset i)) ((normalize 1 (1))))))).
 transitivity (normalize 1 (to_Zpos (word_443 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_443_size.
 -
 rewrite ?scalar_integer_443.
 rewrite ?slice_integer_442.
 rewrite ?(leaf_1_integer s i ghost).
 have literal_0 : to_Zpos [::false] = 0 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 1 1 = 1 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_415_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_448_reference s i ghost : to_Zpos (word_448 (encoded_leaves s i ghost)) = Reference.v432 s i.
Proof.
 change (to_Zpos (word_448 (encoded_leaves s i ghost)) = (normalize 1 (if (Z.eqb (normalize 3 (Reference.r11_npreviousState s)) ((normalize 3 (1)))) then 1 else 0))).
 transitivity (normalize 1 (to_Zpos (word_448 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_448_size.
 -
 rewrite ?scalar_integer_448.
 rewrite ?(leaf_446_integer s i ghost).
 have literal_0 : to_Zpos [::true; false; false] = 1 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 3 1 = 1 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_432_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_449_reference s i ghost : to_Zpos (word_449 (encoded_leaves s i ghost)) = Reference.v6 s i.
Proof.
 change (to_Zpos (word_449 (encoded_leaves s i ghost)) = (normalize 1 (if (Z.eqb (normalize 3 (Reference.r0_nstate s)) ((normalize 3 (2)))) then 1 else 0))).
 transitivity (normalize 1 (to_Zpos (word_449 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_449_size.
 -
 rewrite ?scalar_integer_449.
 rewrite ?(leaf_13_integer s i ghost).
 have literal_0 : to_Zpos [::false; true; false] = 2 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 3 2 = 2 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_6_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_451_reference s i ghost : to_Zpos (word_451 (encoded_leaves s i ghost)) = Reference.v415 s i.
Proof.
 change (to_Zpos (word_451 (encoded_leaves s i ghost)) = (normalize 1 ((Z.lxor (normalize 1 (Reference.nreset i)) ((normalize 1 (1))))))).
 transitivity (normalize 1 (to_Zpos (word_451 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_451_size.
 -
 rewrite ?scalar_integer_451.
 rewrite ?slice_integer_450.
 rewrite ?(leaf_1_integer s i ghost).
 have literal_0 : to_Zpos [::false] = 0 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 1 1 = 1 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_415_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_453_reference s i ghost : to_Zpos (word_453 (encoded_leaves s i ghost)) = Reference.v434 s i.
Proof.
 change (to_Zpos (word_453 (encoded_leaves s i ghost)) = (normalize 1 (if (Z.eqb (normalize 3 (Reference.r11_npreviousState s)) ((normalize 3 (2)))) then 1 else 0))).
 transitivity (normalize 1 (to_Zpos (word_453 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_453_size.
 -
 rewrite ?scalar_integer_453.
 rewrite ?(leaf_446_integer s i ghost).
 have literal_0 : to_Zpos [::false; true; false] = 2 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 3 2 = 2 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_434_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_454_reference s i ghost : to_Zpos (word_454 (encoded_leaves s i ghost)) = Reference.v8 s i.
Proof.
 change (to_Zpos (word_454 (encoded_leaves s i ghost)) = (normalize 1 (if (Z.eqb (normalize 3 (Reference.r0_nstate s)) ((normalize 3 (3)))) then 1 else 0))).
 transitivity (normalize 1 (to_Zpos (word_454 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_454_size.
 -
 rewrite ?scalar_integer_454.
 rewrite ?(leaf_13_integer s i ghost).
 have literal_0 : to_Zpos [::true; true; false] = 3 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 3 3 = 3 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_8_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_456_reference s i ghost : to_Zpos (word_456 (encoded_leaves s i ghost)) = Reference.v415 s i.
Proof.
 change (to_Zpos (word_456 (encoded_leaves s i ghost)) = (normalize 1 ((Z.lxor (normalize 1 (Reference.nreset i)) ((normalize 1 (1))))))).
 transitivity (normalize 1 (to_Zpos (word_456 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_456_size.
 -
 rewrite ?scalar_integer_456.
 rewrite ?slice_integer_455.
 rewrite ?(leaf_1_integer s i ghost).
 have literal_0 : to_Zpos [::false] = 0 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 1 1 = 1 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_415_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_457_reference s i ghost : to_Zpos (word_457 (encoded_leaves s i ghost)) = Reference.v392 s i.
Proof.
 change (to_Zpos (word_457 (encoded_leaves s i ghost)) = (normalize 1 ((Z.lxor ((Reference.v8 s i)) ((normalize 1 (1))))))).
 transitivity (normalize 1 (to_Zpos (word_457 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_457_size.
 -
 rewrite ?scalar_integer_457.
 rewrite ?(control_454_reference s i ghost).
 have literal_0 : to_Zpos [::false] = 0 by reflexivity.
 rewrite ?literal_0.
 have literal_1 : to_Zpos [::true; true; false] = 3 by reflexivity.
 rewrite ?literal_1.
 have constant_0 : normalize 1 1 = 1 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_8_widen; [|lia]).
 rewrite ?(known_bit_eq_zero _ (reference_8_normalized s i)).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_392_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_458_reference s i ghost : to_Zpos (word_458 (encoded_leaves s i ghost)) = Reference.v439 s i.
Proof.
 change (to_Zpos (word_458 (encoded_leaves s i ghost)) = (normalize 1 (if (Z.eqb (normalize 3 (Reference.r11_npreviousState s)) ((normalize 3 (3)))) then 1 else 0))).
 transitivity (normalize 1 (to_Zpos (word_458 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_458_size.
 -
 rewrite ?scalar_integer_458.
 rewrite ?(leaf_446_integer s i ghost).
 have literal_0 : to_Zpos [::true; true; false] = 3 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 3 3 = 3 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_439_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_459_reference s i ghost : to_Zpos (word_459 (encoded_leaves s i ghost)) = Reference.v436 s i.
Proof.
 change (to_Zpos (word_459 (encoded_leaves s i ghost)) = (normalize 1 (if (Z.eqb (normalize 6 (Reference.r12_npreviousCount s)) ((normalize 6 (63)))) then 1 else 0))).
 transitivity (normalize 1 (to_Zpos (word_459 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_459_size.
 -
 rewrite ?scalar_integer_459.
 rewrite ?(leaf_447_integer s i ghost).
 have literal_0 : to_Zpos [::true; true; true; true; true; true] = 63 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 6 63 = 63 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_436_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_460_reference s i ghost : to_Zpos (word_460 (encoded_leaves s i ghost)) = Reference.v437 s i.
Proof.
 change (to_Zpos (word_460 (encoded_leaves s i ghost)) = (normalize 3 (if Z.eqb ((Reference.v436 s i)) 1 then ((normalize 3 (4))) else ((normalize 3 (3)))))).
 transitivity (normalize 3 (to_Zpos (word_460 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_460_size.
 -
 rewrite ?mux_integer_460.
 rewrite ?(control_459_reference s i ghost).
 have literal_0 : to_Zpos [::false; false; true] = 4 by reflexivity.
 rewrite ?literal_0.
 have literal_1 : to_Zpos [::true; true; false] = 3 by reflexivity.
 rewrite ?literal_1.
 have literal_2 : to_Zpos [::true; true; true; true; true; true] = 63 by reflexivity.
 rewrite ?literal_2.
 have constant_0 : normalize 3 3 = 3 by reflexivity.
 rewrite ?constant_0.
 have constant_1 : normalize 3 4 = 4 by reflexivity.
 rewrite ?constant_1.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_436_widen; [|lia]).
 rewrite ?(known_bit_eq_zero _ (reference_436_normalized s i)).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_437_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 3)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_461_reference s i ghost : to_Zpos (word_461 (encoded_leaves s i ghost)) = Reference.v438 s i.
Proof.
 change (to_Zpos (word_461 (encoded_leaves s i ghost)) = (normalize 1 (if (Z.eqb (normalize 3 (Reference.r0_nstate s)) ((Reference.v437 s i))) then 1 else 0))).
 transitivity (normalize 1 (to_Zpos (word_461 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_461_size.
 -
 rewrite ?scalar_integer_461.
 rewrite ?(leaf_13_integer s i ghost).
 rewrite ?(control_460_reference s i ghost).
 have literal_0 : to_Zpos [::false; false; true] = 4 by reflexivity.
 rewrite ?literal_0.
 have literal_1 : to_Zpos [::true; true; false] = 3 by reflexivity.
 rewrite ?literal_1.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_437_widen; [|lia]).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_438_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_463_reference s i ghost : to_Zpos (word_463 (encoded_leaves s i ghost)) = Reference.v415 s i.
Proof.
 change (to_Zpos (word_463 (encoded_leaves s i ghost)) = (normalize 1 ((Z.lxor (normalize 1 (Reference.nreset i)) ((normalize 1 (1))))))).
 transitivity (normalize 1 (to_Zpos (word_463 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_463_size.
 -
 rewrite ?scalar_integer_463.
 rewrite ?slice_integer_462.
 rewrite ?(leaf_1_integer s i ghost).
 have literal_0 : to_Zpos [::false] = 0 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 1 1 = 1 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_415_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_465_reference s i ghost : to_Zpos (word_465 (encoded_leaves s i ghost)) = Reference.v436 s i.
Proof.
 change (to_Zpos (word_465 (encoded_leaves s i ghost)) = (normalize 1 (if (Z.eqb (normalize 6 (Reference.r12_npreviousCount s)) ((normalize 6 (63)))) then 1 else 0))).
 transitivity (normalize 1 (to_Zpos (word_465 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_465_size.
 -
 rewrite ?scalar_integer_465.
 rewrite ?(leaf_447_integer s i ghost).
 have literal_0 : to_Zpos [::true; true; true; true; true; true] = 63 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 6 63 = 63 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_436_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_467_reference s i ghost : to_Zpos (word_467 (encoded_leaves s i ghost)) = Reference.v441 s i.
Proof.
 change (to_Zpos (word_467 (encoded_leaves s i ghost)) = (normalize 6 ((Z.add (normalize 6 (Reference.r12_npreviousCount s)) ((normalize 6 (1))))))).
 transitivity (normalize 6 (to_Zpos (word_467 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_467_size.
 -
 rewrite ?slice_integer_467.
 rewrite ?scalar_integer_466.
 rewrite ?(leaf_447_integer s i ghost).
 have literal_0 : to_Zpos [::true] = 1 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 6 1 = 1 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_441_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 6)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_468_reference s i ghost : to_Zpos (word_468 (encoded_leaves s i ghost)) = Reference.v442 s i.
Proof.
 change (to_Zpos (word_468 (encoded_leaves s i ghost)) = (normalize 6 (if Z.eqb ((Reference.v436 s i)) 1 then ((normalize 6 (0))) else ((Reference.v441 s i))))).
 transitivity (normalize 6 (to_Zpos (word_468 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_468_size.
 -
 rewrite ?mux_integer_468.
 rewrite ?(control_465_reference s i ghost).
 rewrite ?(control_467_reference s i ghost).
 have literal_0 : to_Zpos [::false] = 0 by reflexivity.
 rewrite ?literal_0.
 have literal_1 : to_Zpos [::true; true; true; true; true; true] = 63 by reflexivity.
 rewrite ?literal_1.
 have constant_0 : normalize 6 0 = 0 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_436_widen; [|lia]).
 rewrite ?(known_bit_eq_zero _ (reference_436_normalized s i)).
 repeat (rewrite reference_441_widen; [|lia]).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_442_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 6)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_469_reference s i ghost : to_Zpos (word_469 (encoded_leaves s i ghost)) = Reference.v443 s i.
Proof.
 change (to_Zpos (word_469 (encoded_leaves s i ghost)) = (normalize 1 (if (Z.eqb (normalize 6 (Reference.r9_ncnt_5Fvalue s)) ((Reference.v442 s i))) then 1 else 0))).
 transitivity (normalize 1 (to_Zpos (word_469 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_469_size.
 -
 rewrite ?scalar_integer_469.
 rewrite ?(leaf_51_integer s i ghost).
 rewrite ?(control_468_reference s i ghost).
 have literal_0 : to_Zpos [::false] = 0 by reflexivity.
 rewrite ?literal_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_442_widen; [|lia]).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_443_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_471_reference s i ghost : to_Zpos (word_471 (encoded_leaves s i ghost)) = Reference.v415 s i.
Proof.
 change (to_Zpos (word_471 (encoded_leaves s i ghost)) = (normalize 1 ((Z.lxor (normalize 1 (Reference.nreset i)) ((normalize 1 (1))))))).
 transitivity (normalize 1 (to_Zpos (word_471 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_471_size.
 -
 rewrite ?scalar_integer_471.
 rewrite ?slice_integer_470.
 rewrite ?(leaf_1_integer s i ghost).
 have literal_0 : to_Zpos [::false] = 0 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 1 1 = 1 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_415_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_473_reference s i ghost : to_Zpos (word_473 (encoded_leaves s i ghost)) = Reference.v400 s i.
Proof.
 change (to_Zpos (word_473 (encoded_leaves s i ghost)) = (normalize 1 ((Z.lxor (normalize 1 (Reference.nio_5Fout_5Fready i)) ((normalize 1 (1))))))).
 transitivity (normalize 1 (to_Zpos (word_473 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_473_size.
 -
 rewrite ?scalar_integer_473.
 rewrite ?(leaf_7_integer s i ghost).
 have literal_0 : to_Zpos [::false] = 0 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 1 1 = 1 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_400_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_8_reference s i ghost : to_Zpos (word_8 (encoded_leaves s i ghost)) = Reference.v13 s i.
Proof.
 change (to_Zpos (word_8 (encoded_leaves s i ghost)) = (Reference.v13 s i)).
 transitivity (normalize 1 (to_Zpos (word_8 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_8_size.
 -
 rewrite ?alias_8_shape.
 rewrite ?(control_419_reference s i ghost).
 have literal_0 : to_Zpos [::false; false; true] = 4 by reflexivity.
 rewrite ?literal_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_13_widen; [|lia]).
 rewrite ?(known_bit_eq_zero _ (reference_13_normalized s i)).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_13_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_474_reference s i ghost : to_Zpos (word_474 (encoded_leaves s i ghost)) = Reference.v401 s i.
Proof.
 change (to_Zpos (word_474 (encoded_leaves s i ghost)) = (normalize 1 ((Z.land ((Reference.v13 s i)) ((Reference.v400 s i)))))).
 transitivity (normalize 1 (to_Zpos (word_474 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_474_size.
 -
 rewrite ?scalar_integer_474.
 rewrite ?(control_8_reference s i ghost).
 rewrite ?(control_473_reference s i ghost).
 have literal_0 : to_Zpos [::false] = 0 by reflexivity.
 rewrite ?literal_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 repeat (rewrite reference_13_widen; [|lia]).
 rewrite ?(known_bit_eq_zero _ (reference_13_normalized s i)).
 repeat (rewrite reference_400_widen; [|lia]).
 rewrite ?(known_bit_eq_zero _ (reference_400_normalized s i)).
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_401_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_478_reference s i ghost : to_Zpos (word_478 (encoded_leaves s i ghost)) = Reference.v415 s i.
Proof.
 change (to_Zpos (word_478 (encoded_leaves s i ghost)) = (normalize 1 ((Z.lxor (normalize 1 (Reference.nreset i)) ((normalize 1 (1))))))).
 transitivity (normalize 1 (to_Zpos (word_478 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_478_size.
 -
 rewrite ?scalar_integer_478.
 rewrite ?slice_integer_477.
 rewrite ?(leaf_1_integer s i ghost).
 have literal_0 : to_Zpos [::false] = 0 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 1 1 = 1 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_415_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Lemma control_482_reference s i ghost : to_Zpos (word_482 (encoded_leaves s i ghost)) = Reference.v415 s i.
Proof.
 change (to_Zpos (word_482 (encoded_leaves s i ghost)) = (normalize 1 ((Z.lxor (normalize 1 (Reference.nreset i)) ((normalize 1 (1))))))).
 transitivity (normalize 1 (to_Zpos (word_482 (encoded_leaves s i ghost)))).
 - symmetry. apply unsigned_normalized. apply encoded_word_482_size.
 -
 rewrite ?scalar_integer_482.
 rewrite ?slice_integer_481.
 rewrite ?(leaf_1_integer s i ghost).
 have literal_0 : to_Zpos [::false] = 0 by reflexivity.
 rewrite ?literal_0.
 have constant_0 : normalize 1 1 = 1 by reflexivity.
 rewrite ?constant_0.
 rewrite ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?Z.shiftr_0_r ?normalize_zero ?Z.shiftl_0_l ?Z.add_0_l ?Z.add_0_r.
 rewrite ?(le_successor_lt _ 62).
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]].
 rewrite ?normalized_eq_zero.
 repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb a b) | |- context [Z.ltb ?a ?b] => destruct (Z.ltb a b) | |- context [Z.leb ?a ?b] => destruct (Z.leb a b) end; cbn [negb];
 repeat first [rewrite normalize_nested; [|lia] | rewrite normalize_widen; [|lia]];
 rewrite ?reference_415_normalized; try reflexivity.
 all: try (rewrite Z.shiftl_mul_pow2; [|lia]); try reflexivity.
 all: try (apply (f_equal (normalize 1)); apply Z.land_comm).
 all: reflexivity.
Qed.
Print Assumptions control_482_reference.
