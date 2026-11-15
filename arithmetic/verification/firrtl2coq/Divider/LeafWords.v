From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Types SsrOrder Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths.
From ArithmeticCommon Require Import BitvectorFacts.
From Divider Require Import Stable Representation.
Local Open Scope Z_scope.
Lemma normalize_widen outer inner z (ordered : (inner <= outer)%coq_nat) : normalize outer (normalize inner z) = normalize inner z.
Proof.
 apply Z.mod_small. pose proof (normalize_range inner z) as bounds.
 assert (power : modulus inner <= modulus outer).
 { unfold modulus. apply Z.pow_le_mono_r; lia. }
 lia.
Qed.

Transparent word_0.
Lemma leaf_0_integer s i ghost : to_Zpos (word_0 (encoded_leaves s i ghost)) = normalize 1 1.
Proof. unfold word_0, encoded_leaves. apply decode_encode. Qed.
Opaque word_0.
Transparent word_1.
Lemma leaf_1_integer s i ghost : to_Zpos (word_1 (encoded_leaves s i ghost)) = normalize 1 (Reference.nreset i).
Proof. unfold word_1, encoded_leaves. apply decode_encode. Qed.
Opaque word_1.
Transparent word_3.
Lemma leaf_3_integer s i ghost : to_Zpos (word_3 (encoded_leaves s i ghost)) = normalize 1 (Reference.nio_5Fin_5Fvalid i).
Proof. unfold word_3, encoded_leaves. apply decode_encode. Qed.
Opaque word_3.
Transparent word_4.
Lemma leaf_4_integer s i ghost : to_Zpos (word_4 (encoded_leaves s i ghost)) = normalize 64 (Reference.nio_5Fin_5Fbits_5Fsrc_5F0 i).
Proof. unfold word_4, encoded_leaves. apply decode_encode. Qed.
Opaque word_4.
Transparent word_5.
Lemma leaf_5_integer s i ghost : to_Zpos (word_5 (encoded_leaves s i ghost)) = normalize 64 (Reference.nio_5Fin_5Fbits_5Fsrc_5F1 i).
Proof. unfold word_5, encoded_leaves. apply decode_encode. Qed.
Opaque word_5.
Transparent word_6.
Lemma leaf_6_integer s i ghost : to_Zpos (word_6 (encoded_leaves s i ghost)) = normalize 64 (Reference.nio_5Fin_5Fbits_5Fsrc_5F2 i).
Proof. unfold word_6, encoded_leaves. apply decode_encode. Qed.
Opaque word_6.
Transparent word_7.
Lemma leaf_7_integer s i ghost : to_Zpos (word_7 (encoded_leaves s i ghost)) = normalize 1 (Reference.nio_5Fout_5Fready i).
Proof. unfold word_7, encoded_leaves. apply decode_encode. Qed.
Opaque word_7.
Transparent word_10.
Lemma leaf_10_integer s i ghost : to_Zpos (word_10 (encoded_leaves s i ghost)) = normalize 1 (Reference.nctrl_5Fsign i).
Proof. unfold word_10, encoded_leaves. apply decode_encode. Qed.
Opaque word_10.
Transparent word_11.
Lemma leaf_11_integer s i ghost : to_Zpos (word_11 (encoded_leaves s i ghost)) = normalize 1 (Reference.nctrl_5FisW i).
Proof. unfold word_11, encoded_leaves. apply decode_encode. Qed.
Opaque word_11.
Transparent word_12.
Lemma leaf_12_integer s i ghost : to_Zpos (word_12 (encoded_leaves s i ghost)) = normalize 1 (Reference.nctrl_5FisHi i).
Proof. unfold word_12, encoded_leaves. apply decode_encode. Qed.
Opaque word_12.
Transparent word_13.
Lemma leaf_13_integer s i ghost : to_Zpos (word_13 (encoded_leaves s i ghost)) = normalize 3 (Reference.r0_nstate s).
Proof. unfold word_13, encoded_leaves. apply decode_encode. Qed.
Opaque word_13.
Transparent word_18.
Lemma leaf_18_integer s i ghost : to_Zpos (word_18 (encoded_leaves s i ghost)) = normalize 1 (Reference.r1_ndivBy0Reg s).
Proof. unfold word_18, encoded_leaves. apply decode_encode. Qed.
Opaque word_18.
Transparent word_20.
Lemma leaf_20_integer s i ghost : to_Zpos (word_20 (encoded_leaves s i ghost)) = normalize 129 (Reference.r2_nshiftReg s).
Proof. unfold word_20, encoded_leaves. apply decode_encode. Qed.
Opaque word_20.
Transparent word_33.
Lemma leaf_33_integer s i ghost : to_Zpos (word_33 (encoded_leaves s i ghost)) = normalize 1 (Reference.r3_naSignReg s).
Proof. unfold word_33, encoded_leaves. apply decode_encode. Qed.
Opaque word_33.
Transparent word_38.
Lemma leaf_38_integer s i ghost : to_Zpos (word_38 (encoded_leaves s i ghost)) = normalize 1 (Reference.r4_nqSignReg s).
Proof. unfold word_38, encoded_leaves. apply decode_encode. Qed.
Opaque word_38.
Transparent word_40.
Lemma leaf_40_integer s i ghost : to_Zpos (word_40 (encoded_leaves s i ghost)) = normalize 64 (Reference.r5_nbReg s).
Proof. unfold word_40, encoded_leaves. apply decode_encode. Qed.
Opaque word_40.
Lemma leaf_40_reference s i ghost : to_Zpos (word_40 (encoded_leaves s i ghost)) = Reference.v34 s i.
Proof. rewrite leaf_40_integer. unfold Reference.v34, Reference.v26, Radix2Divider.CIRCTBits.word.
 change (normalize 64 (Reference.r5_nbReg s) = normalize 65 (normalize 64 (Reference.r5_nbReg s))).
 symmetry. apply normalize_widen. lia. Qed.
Transparent word_43.
Lemma leaf_43_integer s i ghost : to_Zpos (word_43 (encoded_leaves s i ghost)) = normalize 65 (Reference.r6_naValx2Reg s).
Proof. unfold word_43, encoded_leaves. apply decode_encode. Qed.
Opaque word_43.
Lemma leaf_43_reference s i ghost : to_Zpos (word_43 (encoded_leaves s i ghost)) = Reference.v28 s i.
Proof. rewrite leaf_43_integer. unfold Reference.v28, Reference.v27, Radix2Divider.CIRCTBits.word.
 change (normalize 65 (Reference.r6_naValx2Reg s) = normalize 128 (normalize 65 (Reference.r6_naValx2Reg s))).
 symmetry. apply normalize_widen. lia. Qed.
Transparent word_45.
Lemma leaf_45_integer s i ghost : to_Zpos (word_45 (encoded_leaves s i ghost)) = normalize 1 ghost.
Proof. unfold word_45, encoded_leaves. apply decode_encode. Qed.
Opaque word_45.
Transparent word_46.
Lemma leaf_46_integer s i ghost : to_Zpos (word_46 (encoded_leaves s i ghost)) = normalize 1 (Reference.r7_nctrlReg_5FisW s).
Proof. unfold word_46, encoded_leaves. apply decode_encode. Qed.
Opaque word_46.
Transparent word_47.
Lemma leaf_47_integer s i ghost : to_Zpos (word_47 (encoded_leaves s i ghost)) = normalize 1 (Reference.r8_nctrlReg_5FisHi s).
Proof. unfold word_47, encoded_leaves. apply decode_encode. Qed.
Opaque word_47.
Transparent word_51.
Lemma leaf_51_integer s i ghost : to_Zpos (word_51 (encoded_leaves s i ghost)) = normalize 6 (Reference.r9_ncnt_5Fvalue s).
Proof. unfold word_51, encoded_leaves. apply decode_encode. Qed.
Opaque word_51.
Lemma leaf_51_reference s i ghost : to_Zpos (word_51 (encoded_leaves s i ghost)) = Reference.v30 s i.
Proof. rewrite leaf_51_integer. unfold Reference.v30, Reference.v29, Radix2Divider.CIRCTBits.word.
 change (normalize 6 (Reference.r9_ncnt_5Fvalue s) = normalize 128 (normalize 6 (Reference.r9_ncnt_5Fvalue s))).
 symmetry. apply normalize_widen. lia. Qed.
Transparent word_445.
Lemma leaf_445_integer s i ghost : to_Zpos (word_445 (encoded_leaves s i ghost)) = normalize 1 (Reference.r10_nhistoryValid s).
Proof. unfold word_445, encoded_leaves. apply decode_encode. Qed.
Opaque word_445.
Transparent word_446.
Lemma leaf_446_integer s i ghost : to_Zpos (word_446 (encoded_leaves s i ghost)) = normalize 3 (Reference.r11_npreviousState s).
Proof. unfold word_446, encoded_leaves. apply decode_encode. Qed.
Opaque word_446.
Transparent word_447.
Lemma leaf_447_integer s i ghost : to_Zpos (word_447 (encoded_leaves s i ghost)) = normalize 6 (Reference.r12_npreviousCount s).
Proof. unfold word_447, encoded_leaves. apply decode_encode. Qed.
Opaque word_447.
Transparent word_475.
Lemma leaf_475_integer s i ghost : to_Zpos (word_475 (encoded_leaves s i ghost)) = normalize 1 (Reference.r13_nwasStalled s).
Proof. unfold word_475, encoded_leaves. apply decode_encode. Qed.
Opaque word_475.
Transparent word_476.
Lemma leaf_476_integer s i ghost : to_Zpos (word_476 (encoded_leaves s i ghost)) = normalize 64 (Reference.r14_npreviousOutput s).
Proof. unfold word_476, encoded_leaves. apply decode_encode. Qed.
Opaque word_476.
Transparent word_2.
Lemma alias_2_shape v : word_2 v = word_420 v.
Proof. unfold word_2, closed_2, expr_2, word_of_eval. reflexivity. Qed.
Opaque word_2.
Transparent word_8.
Lemma alias_8_shape v : word_8 v = word_419 v.
Proof. unfold word_8, closed_8, expr_8, word_of_eval. reflexivity. Qed.
Opaque word_8.
Transparent word_9.
Lemma alias_9_shape v : word_9 v = word_418 v.
Proof. unfold word_9, closed_9, expr_9, word_of_eval. reflexivity. Qed.
Opaque word_9.
Transparent word_376.
Lemma shift_376_shape v : word_376 v = zext_to 128 (zeros (to_nat (word_51 v)) ++ word_43 v).
Proof. unfold word_376, closed_376, expr_376, word_of_eval. reflexivity. Qed.
Opaque word_376.
Lemma shift_376_integer s i ghost : to_Zpos (word_376 (encoded_leaves s i ghost)) =
 Z.shiftl (to_Zpos (word_43 (encoded_leaves s i ghost))) (to_Zpos (word_51 (encoded_leaves s i ghost))).
Proof. rewrite shift_376_shape. unfold zext_to. rewrite unsigned_zero_extend unsigned_shift_left.
 rewrite -to_Zpos_nat. reflexivity. Qed.
Print Assumptions shift_376_integer.

