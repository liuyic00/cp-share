(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

Lemma node_0 (s : N.State) (i : N.Inputs) :
  R.v0 (state s) (inputs i) = Zmod.unsigned (N.v0 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v0 s i)) at 1.
  unfold R.v0, N.v0.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_1 (s : N.State) (i : N.Inputs) :
  R.v1 (state s) (inputs i) = Zmod.unsigned (N.v1 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v1 s i)) at 1.
  unfold R.v1, N.v1.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_2 (s : N.State) (i : N.Inputs) :
  R.v2 (state s) (inputs i) = Zmod.unsigned (N.v2 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v2 s i)) at 1.
  unfold R.v2, N.v2.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_3 (s : N.State) (i : N.Inputs) :
  R.v3 (state s) (inputs i) = Zmod.unsigned (N.v3 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v3 s i)) at 1.
  unfold R.v3, N.v3.
  unfold R.v2, N.v2.
  rewrite !inputs_nio_5Fb.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fb i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_4 (s : N.State) (i : N.Inputs) :
  R.v4 (state s) (inputs i) = Zmod.unsigned (N.v4 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v4 s i)) at 1.
  unfold R.v4, N.v4.
  rewrite ?node_3.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_5 (s : N.State) (i : N.Inputs) :
  R.v5 (state s) (inputs i) = Zmod.unsigned (N.v5 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v5 s i)) at 1.
  unfold R.v5, N.v5.
  rewrite ?node_3.
  rewrite ?node_4.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_6 (s : N.State) (i : N.Inputs) :
  R.v6 (state s) (inputs i) = Zmod.unsigned (N.v6 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v6 s i)) at 1.
  unfold R.v6, N.v6.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_7 (s : N.State) (i : N.Inputs) :
  R.v7 (state s) (inputs i) = Zmod.unsigned (N.v7 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v7 s i)) at 1.
  unfold R.v7, N.v7.
  rewrite ?node_3.
  unfold R.v6, N.v6.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_8 (s : N.State) (i : N.Inputs) :
  R.v8 (state s) (inputs i) = Zmod.unsigned (N.v8 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v8 s i)) at 1.
  unfold R.v8, N.v8.
  rewrite ?node_1.
  rewrite ?node_5.
  rewrite ?node_7.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_9 (s : N.State) (i : N.Inputs) :
  R.v9 (state s) (inputs i) = Zmod.unsigned (N.v9 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v9 s i)) at 1.
  unfold R.v9, N.v9.
  rewrite !inputs_nio_5Fb.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fb i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_10 (s : N.State) (i : N.Inputs) :
  R.v10 (state s) (inputs i) = Zmod.unsigned (N.v10 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v10 s i)) at 1.
  unfold R.v10, N.v10.
  rewrite ?node_9.
  rewrite !inputs_nio_5Fb.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fb i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_11 (s : N.State) (i : N.Inputs) :
  R.v11 (state s) (inputs i) = Zmod.unsigned (N.v11 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v11 s i)) at 1.
  unfold R.v11, N.v11.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_12 (s : N.State) (i : N.Inputs) :
  R.v12 (state s) (inputs i) = Zmod.unsigned (N.v12 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v12 s i)) at 1.
  unfold R.v12, N.v12.
  rewrite ?node_1.
  rewrite ?node_10.
  unfold R.v11, N.v11.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_13 (s : N.State) (i : N.Inputs) :
  R.v13 (state s) (inputs i) = Zmod.unsigned (N.v13 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v13 s i)) at 1.
  unfold R.v13, N.v13.
  rewrite ?node_0.
  rewrite ?node_8.
  rewrite ?node_12.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_14 (s : N.State) (i : N.Inputs) :
  R.v14 (state s) (inputs i) = Zmod.unsigned (N.v14 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v14 s i)) at 1.
  unfold R.v14, N.v14.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_15 (s : N.State) (i : N.Inputs) :
  R.v15 (state s) (inputs i) = Zmod.unsigned (N.v15 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v15 s i)) at 1.
  unfold R.v15, N.v15.
  rewrite ?node_14.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r0_nr.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r0_nr s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_16 (s : N.State) (i : N.Inputs) :
  R.v16 (state s) (inputs i) = Zmod.unsigned (N.v16 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v16 s i)) at 1.
  unfold R.v16, N.v16.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_17 (s : N.State) (i : N.Inputs) :
  R.v17 (state s) (inputs i) = Zmod.unsigned (N.v17 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v17 s i)) at 1.
  unfold R.v17, N.v17.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_18 (s : N.State) (i : N.Inputs) :
  R.v18 (state s) (inputs i) = Zmod.unsigned (N.v18 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v18 s i)) at 1.
  unfold R.v18, N.v18.
  rewrite ?node_16.
  unfold R.v17, N.v17.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_19 (s : N.State) (i : N.Inputs) :
  R.v19 (state s) (inputs i) = Zmod.unsigned (N.v19 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v19 s i)) at 1.
  unfold R.v19, N.v19.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_20 (s : N.State) (i : N.Inputs) :
  R.v20 (state s) (inputs i) = Zmod.unsigned (N.v20 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v20 s i)) at 1.
  unfold R.v20, N.v20.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_21 (s : N.State) (i : N.Inputs) :
  R.v21 (state s) (inputs i) = Zmod.unsigned (N.v21 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v21 s i)) at 1.
  unfold R.v21, N.v21.
  rewrite ?node_16.
  unfold R.v20, N.v20.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22 (s : N.State) (i : N.Inputs) :
  R.v22 (state s) (inputs i) = Zmod.unsigned (N.v22 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22 s i)) at 1.
  unfold R.v22, N.v22.
  unfold R.v6, N.v6.
  rewrite ?node_21.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23 (s : N.State) (i : N.Inputs) :
  R.v23 (state s) (inputs i) = Zmod.unsigned (N.v23 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23 s i)) at 1.
  unfold R.v23, N.v23.
  rewrite ?node_18.
  unfold R.v19, N.v19.
  rewrite ?node_22.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24 (s : N.State) (i : N.Inputs) :
  R.v24 (state s) (inputs i) = Zmod.unsigned (N.v24 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24 s i)) at 1.
  unfold R.v24, N.v24.
  rewrite ?node_23.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_25 (s : N.State) (i : N.Inputs) :
  R.v25 (state s) (inputs i) = Zmod.unsigned (N.v25 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v25 s i)) at 1.
  unfold R.v25, N.v25.
  rewrite ?node_24.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r1_nr_5F1.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r1_nr_5F1 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26 (s : N.State) (i : N.Inputs) :
  R.v26 (state s) (inputs i) = Zmod.unsigned (N.v26 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26 s i)) at 1.
  unfold R.v26, N.v26.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_27 (s : N.State) (i : N.Inputs) :
  R.v27 (state s) (inputs i) = Zmod.unsigned (N.v27 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v27 s i)) at 1.
  unfold R.v27, N.v27.
  rewrite ?node_26.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r2_nr_5F2.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r2_nr_5F2 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_28 (s : N.State) (i : N.Inputs) :
  R.v28 (state s) (inputs i) = Zmod.unsigned (N.v28 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v28 s i)) at 1.
  unfold R.v28, N.v28.
  rewrite ?node_23.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_29 (s : N.State) (i : N.Inputs) :
  R.v29 (state s) (inputs i) = Zmod.unsigned (N.v29 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v29 s i)) at 1.
  unfold R.v29, N.v29.
  rewrite ?node_28.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r3_nr_5F3.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r3_nr_5F3 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_30 (s : N.State) (i : N.Inputs) :
  R.v30 (state s) (inputs i) = Zmod.unsigned (N.v30 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v30 s i)) at 1.
  unfold R.v30, N.v30.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_31 (s : N.State) (i : N.Inputs) :
  R.v31 (state s) (inputs i) = Zmod.unsigned (N.v31 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v31 s i)) at 1.
  unfold R.v31, N.v31.
  rewrite ?node_30.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r4_nr_5F4.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r4_nr_5F4 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_32 (s : N.State) (i : N.Inputs) :
  R.v32 (state s) (inputs i) = Zmod.unsigned (N.v32 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v32 s i)) at 1.
  unfold R.v32, N.v32.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_33 (s : N.State) (i : N.Inputs) :
  R.v33 (state s) (inputs i) = Zmod.unsigned (N.v33 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v33 s i)) at 1.
  unfold R.v33, N.v33.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_34 (s : N.State) (i : N.Inputs) :
  R.v34 (state s) (inputs i) = Zmod.unsigned (N.v34 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v34 s i)) at 1.
  unfold R.v34, N.v34.
  rewrite ?node_32.
  unfold R.v33, N.v33.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_35 (s : N.State) (i : N.Inputs) :
  R.v35 (state s) (inputs i) = Zmod.unsigned (N.v35 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v35 s i)) at 1.
  unfold R.v35, N.v35.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_36 (s : N.State) (i : N.Inputs) :
  R.v36 (state s) (inputs i) = Zmod.unsigned (N.v36 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v36 s i)) at 1.
  unfold R.v36, N.v36.
  rewrite ?node_32.
  unfold R.v35, N.v35.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_37 (s : N.State) (i : N.Inputs) :
  R.v37 (state s) (inputs i) = Zmod.unsigned (N.v37 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v37 s i)) at 1.
  unfold R.v37, N.v37.
  rewrite ?node_34.
  rewrite ?node_36.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_38 (s : N.State) (i : N.Inputs) :
  R.v38 (state s) (inputs i) = Zmod.unsigned (N.v38 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v38 s i)) at 1.
  unfold R.v38, N.v38.
  rewrite ?node_3.
  rewrite ?node_4.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_39 (s : N.State) (i : N.Inputs) :
  R.v39 (state s) (inputs i) = Zmod.unsigned (N.v39 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v39 s i)) at 1.
  unfold R.v39, N.v39.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_40 (s : N.State) (i : N.Inputs) :
  R.v40 (state s) (inputs i) = Zmod.unsigned (N.v40 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v40 s i)) at 1.
  unfold R.v40, N.v40.
  rewrite ?node_32.
  unfold R.v39, N.v39.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41 (s : N.State) (i : N.Inputs) :
  R.v41 (state s) (inputs i) = Zmod.unsigned (N.v41 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41 s i)) at 1.
  unfold R.v41, N.v41.
  rewrite ?node_3.
  unfold R.v6, N.v6.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_42 (s : N.State) (i : N.Inputs) :
  R.v42 (state s) (inputs i) = Zmod.unsigned (N.v42 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v42 s i)) at 1.
  unfold R.v42, N.v42.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43 (s : N.State) (i : N.Inputs) :
  R.v43 (state s) (inputs i) = Zmod.unsigned (N.v43 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43 s i)) at 1.
  unfold R.v43, N.v43.
  rewrite ?node_32.
  unfold R.v42, N.v42.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44 (s : N.State) (i : N.Inputs) :
  R.v44 (state s) (inputs i) = Zmod.unsigned (N.v44 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44 s i)) at 1.
  unfold R.v44, N.v44.
  unfold R.v6, N.v6.
  rewrite !inputs_nio_5Fb.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fb i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_45 (s : N.State) (i : N.Inputs) :
  R.v45 (state s) (inputs i) = Zmod.unsigned (N.v45 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v45 s i)) at 1.
  unfold R.v45, N.v45.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_46 (s : N.State) (i : N.Inputs) :
  R.v46 (state s) (inputs i) = Zmod.unsigned (N.v46 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v46 s i)) at 1.
  unfold R.v46, N.v46.
  rewrite ?node_32.
  unfold R.v45, N.v45.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_47 (s : N.State) (i : N.Inputs) :
  R.v47 (state s) (inputs i) = Zmod.unsigned (N.v47 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v47 s i)) at 1.
  unfold R.v47, N.v47.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48 (s : N.State) (i : N.Inputs) :
  R.v48 (state s) (inputs i) = Zmod.unsigned (N.v48 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48 s i)) at 1.
  unfold R.v48, N.v48.
  rewrite ?node_32.
  unfold R.v47, N.v47.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_49 (s : N.State) (i : N.Inputs) :
  R.v49 (state s) (inputs i) = Zmod.unsigned (N.v49 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v49 s i)) at 1.
  unfold R.v49, N.v49.
  rewrite ?node_46.
  rewrite ?node_48.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_50 (s : N.State) (i : N.Inputs) :
  R.v50 (state s) (inputs i) = Zmod.unsigned (N.v50 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v50 s i)) at 1.
  unfold R.v50, N.v50.
  rewrite ?node_9.
  rewrite !inputs_nio_5Fb.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fb i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_51 (s : N.State) (i : N.Inputs) :
  R.v51 (state s) (inputs i) = Zmod.unsigned (N.v51 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v51 s i)) at 1.
  unfold R.v51, N.v51.
  unfold R.v11, N.v11.
  rewrite ?node_49.
  rewrite ?node_50.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_52 (s : N.State) (i : N.Inputs) :
  R.v52 (state s) (inputs i) = Zmod.unsigned (N.v52 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v52 s i)) at 1.
  unfold R.v52, N.v52.
  rewrite ?node_43.
  rewrite ?node_44.
  rewrite ?node_51.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_53 (s : N.State) (i : N.Inputs) :
  R.v53 (state s) (inputs i) = Zmod.unsigned (N.v53 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v53 s i)) at 1.
  unfold R.v53, N.v53.
  rewrite ?node_40.
  rewrite ?node_41.
  rewrite ?node_52.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_54 (s : N.State) (i : N.Inputs) :
  R.v54 (state s) (inputs i) = Zmod.unsigned (N.v54 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v54 s i)) at 1.
  unfold R.v54, N.v54.
  rewrite ?node_37.
  rewrite ?node_38.
  rewrite ?node_53.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_55 (s : N.State) (i : N.Inputs) :
  R.v55 (state s) (inputs i) = Zmod.unsigned (N.v55 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v55 s i)) at 1.
  unfold R.v55, N.v55.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_56 (s : N.State) (i : N.Inputs) :
  R.v56 (state s) (inputs i) = Zmod.unsigned (N.v56 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v56 s i)) at 1.
  unfold R.v56, N.v56.
  rewrite ?node_55.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r5_nr_5F5.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r5_nr_5F5 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_57 (s : N.State) (i : N.Inputs) :
  R.v57 (state s) (inputs i) = Zmod.unsigned (N.v57 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v57 s i)) at 1.
  unfold R.v57, N.v57.
  unfold R.v6, N.v6.
  rewrite ?node_40.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58 (s : N.State) (i : N.Inputs) :
  R.v58 (state s) (inputs i) = Zmod.unsigned (N.v58 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58 s i)) at 1.
  unfold R.v58, N.v58.
  unfold R.v19, N.v19.
  rewrite ?node_37.
  rewrite ?node_57.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_59 (s : N.State) (i : N.Inputs) :
  R.v59 (state s) (inputs i) = Zmod.unsigned (N.v59 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v59 s i)) at 1.
  unfold R.v59, N.v59.
  rewrite ?node_58.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_60 (s : N.State) (i : N.Inputs) :
  R.v60 (state s) (inputs i) = Zmod.unsigned (N.v60 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v60 s i)) at 1.
  unfold R.v60, N.v60.
  rewrite ?node_59.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r6_nr_5F6.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r6_nr_5F6 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_61 (s : N.State) (i : N.Inputs) :
  R.v61 (state s) (inputs i) = Zmod.unsigned (N.v61 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v61 s i)) at 1.
  unfold R.v61, N.v61.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_62 (s : N.State) (i : N.Inputs) :
  R.v62 (state s) (inputs i) = Zmod.unsigned (N.v62 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v62 s i)) at 1.
  unfold R.v62, N.v62.
  rewrite ?node_61.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r7_nr_5F7.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r7_nr_5F7 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_63 (s : N.State) (i : N.Inputs) :
  R.v63 (state s) (inputs i) = Zmod.unsigned (N.v63 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v63 s i)) at 1.
  unfold R.v63, N.v63.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_64 (s : N.State) (i : N.Inputs) :
  R.v64 (state s) (inputs i) = Zmod.unsigned (N.v64 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v64 s i)) at 1.
  unfold R.v64, N.v64.
  rewrite ?node_63.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r8_nr_5F8.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r8_nr_5F8 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_65 (s : N.State) (i : N.Inputs) :
  R.v65 (state s) (inputs i) = Zmod.unsigned (N.v65 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v65 s i)) at 1.
  unfold R.v65, N.v65.
  rewrite ?node_58.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_66 (s : N.State) (i : N.Inputs) :
  R.v66 (state s) (inputs i) = Zmod.unsigned (N.v66 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v66 s i)) at 1.
  unfold R.v66, N.v66.
  rewrite ?node_65.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r9_nr_5F9.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r9_nr_5F9 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_67 (s : N.State) (i : N.Inputs) :
  R.v67 (state s) (inputs i) = Zmod.unsigned (N.v67 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v67 s i)) at 1.
  unfold R.v67, N.v67.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_68 (s : N.State) (i : N.Inputs) :
  R.v68 (state s) (inputs i) = Zmod.unsigned (N.v68 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v68 s i)) at 1.
  unfold R.v68, N.v68.
  rewrite ?node_67.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r10_nr_5F10.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r10_nr_5F10 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_69 (s : N.State) (i : N.Inputs) :
  R.v69 (state s) (inputs i) = Zmod.unsigned (N.v69 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v69 s i)) at 1.
  unfold R.v69, N.v69.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_70 (s : N.State) (i : N.Inputs) :
  R.v70 (state s) (inputs i) = Zmod.unsigned (N.v70 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v70 s i)) at 1.
  unfold R.v70, N.v70.
  rewrite ?node_69.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r11_nr_5F11.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r11_nr_5F11 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_71 (s : N.State) (i : N.Inputs) :
  R.v71 (state s) (inputs i) = Zmod.unsigned (N.v71 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v71 s i)) at 1.
  unfold R.v71, N.v71.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_72 (s : N.State) (i : N.Inputs) :
  R.v72 (state s) (inputs i) = Zmod.unsigned (N.v72 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v72 s i)) at 1.
  unfold R.v72, N.v72.
  unfold R.v33, N.v33.
  rewrite ?node_71.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_73 (s : N.State) (i : N.Inputs) :
  R.v73 (state s) (inputs i) = Zmod.unsigned (N.v73 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v73 s i)) at 1.
  unfold R.v73, N.v73.
  unfold R.v35, N.v35.
  rewrite ?node_71.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_74 (s : N.State) (i : N.Inputs) :
  R.v74 (state s) (inputs i) = Zmod.unsigned (N.v74 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v74 s i)) at 1.
  unfold R.v74, N.v74.
  rewrite ?node_72.
  rewrite ?node_73.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_75 (s : N.State) (i : N.Inputs) :
  R.v75 (state s) (inputs i) = Zmod.unsigned (N.v75 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v75 s i)) at 1.
  unfold R.v75, N.v75.
  unfold R.v39, N.v39.
  rewrite ?node_71.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_76 (s : N.State) (i : N.Inputs) :
  R.v76 (state s) (inputs i) = Zmod.unsigned (N.v76 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v76 s i)) at 1.
  unfold R.v76, N.v76.
  unfold R.v42, N.v42.
  rewrite ?node_71.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_77 (s : N.State) (i : N.Inputs) :
  R.v77 (state s) (inputs i) = Zmod.unsigned (N.v77 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v77 s i)) at 1.
  unfold R.v77, N.v77.
  unfold R.v45, N.v45.
  rewrite ?node_71.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_78 (s : N.State) (i : N.Inputs) :
  R.v78 (state s) (inputs i) = Zmod.unsigned (N.v78 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v78 s i)) at 1.
  unfold R.v78, N.v78.
  unfold R.v47, N.v47.
  rewrite ?node_71.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_79 (s : N.State) (i : N.Inputs) :
  R.v79 (state s) (inputs i) = Zmod.unsigned (N.v79 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v79 s i)) at 1.
  unfold R.v79, N.v79.
  rewrite ?node_77.
  rewrite ?node_78.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_80 (s : N.State) (i : N.Inputs) :
  R.v80 (state s) (inputs i) = Zmod.unsigned (N.v80 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v80 s i)) at 1.
  unfold R.v80, N.v80.
  unfold R.v11, N.v11.
  rewrite ?node_50.
  rewrite ?node_79.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_81 (s : N.State) (i : N.Inputs) :
  R.v81 (state s) (inputs i) = Zmod.unsigned (N.v81 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v81 s i)) at 1.
  unfold R.v81, N.v81.
  rewrite ?node_44.
  rewrite ?node_76.
  rewrite ?node_80.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_82 (s : N.State) (i : N.Inputs) :
  R.v82 (state s) (inputs i) = Zmod.unsigned (N.v82 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v82 s i)) at 1.
  unfold R.v82, N.v82.
  rewrite ?node_41.
  rewrite ?node_75.
  rewrite ?node_81.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_83 (s : N.State) (i : N.Inputs) :
  R.v83 (state s) (inputs i) = Zmod.unsigned (N.v83 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v83 s i)) at 1.
  unfold R.v83, N.v83.
  rewrite ?node_38.
  rewrite ?node_74.
  rewrite ?node_82.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_84 (s : N.State) (i : N.Inputs) :
  R.v84 (state s) (inputs i) = Zmod.unsigned (N.v84 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v84 s i)) at 1.
  unfold R.v84, N.v84.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_85 (s : N.State) (i : N.Inputs) :
  R.v85 (state s) (inputs i) = Zmod.unsigned (N.v85 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v85 s i)) at 1.
  unfold R.v85, N.v85.
  rewrite ?node_84.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r12_nr_5F12.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r12_nr_5F12 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_86 (s : N.State) (i : N.Inputs) :
  R.v86 (state s) (inputs i) = Zmod.unsigned (N.v86 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v86 s i)) at 1.
  unfold R.v86, N.v86.
  unfold R.v6, N.v6.
  rewrite ?node_75.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_87 (s : N.State) (i : N.Inputs) :
  R.v87 (state s) (inputs i) = Zmod.unsigned (N.v87 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v87 s i)) at 1.
  unfold R.v87, N.v87.
  unfold R.v19, N.v19.
  rewrite ?node_74.
  rewrite ?node_86.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_88 (s : N.State) (i : N.Inputs) :
  R.v88 (state s) (inputs i) = Zmod.unsigned (N.v88 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v88 s i)) at 1.
  unfold R.v88, N.v88.
  rewrite ?node_87.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_89 (s : N.State) (i : N.Inputs) :
  R.v89 (state s) (inputs i) = Zmod.unsigned (N.v89 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v89 s i)) at 1.
  unfold R.v89, N.v89.
  rewrite ?node_88.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r13_nr_5F13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r13_nr_5F13 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_90 (s : N.State) (i : N.Inputs) :
  R.v90 (state s) (inputs i) = Zmod.unsigned (N.v90 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v90 s i)) at 1.
  unfold R.v90, N.v90.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_91 (s : N.State) (i : N.Inputs) :
  R.v91 (state s) (inputs i) = Zmod.unsigned (N.v91 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v91 s i)) at 1.
  unfold R.v91, N.v91.
  rewrite ?node_90.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r14_nr_5F14.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r14_nr_5F14 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_92 (s : N.State) (i : N.Inputs) :
  R.v92 (state s) (inputs i) = Zmod.unsigned (N.v92 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v92 s i)) at 1.
  unfold R.v92, N.v92.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_93 (s : N.State) (i : N.Inputs) :
  R.v93 (state s) (inputs i) = Zmod.unsigned (N.v93 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v93 s i)) at 1.
  unfold R.v93, N.v93.
  rewrite ?node_92.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r15_nr_5F15.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r15_nr_5F15 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_94 (s : N.State) (i : N.Inputs) :
  R.v94 (state s) (inputs i) = Zmod.unsigned (N.v94 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v94 s i)) at 1.
  unfold R.v94, N.v94.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_95 (s : N.State) (i : N.Inputs) :
  R.v95 (state s) (inputs i) = Zmod.unsigned (N.v95 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v95 s i)) at 1.
  unfold R.v95, N.v95.
  rewrite ?node_94.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r16_nr_5F16.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r16_nr_5F16 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_96 (s : N.State) (i : N.Inputs) :
  R.v96 (state s) (inputs i) = Zmod.unsigned (N.v96 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v96 s i)) at 1.
  unfold R.v96, N.v96.
  rewrite ?node_87.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_97 (s : N.State) (i : N.Inputs) :
  R.v97 (state s) (inputs i) = Zmod.unsigned (N.v97 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v97 s i)) at 1.
  unfold R.v97, N.v97.
  rewrite ?node_96.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r17_nr_5F17.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r17_nr_5F17 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_98 (s : N.State) (i : N.Inputs) :
  R.v98 (state s) (inputs i) = Zmod.unsigned (N.v98 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v98 s i)) at 1.
  unfold R.v98, N.v98.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_99 (s : N.State) (i : N.Inputs) :
  R.v99 (state s) (inputs i) = Zmod.unsigned (N.v99 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v99 s i)) at 1.
  unfold R.v99, N.v99.
  rewrite ?node_98.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r18_nr_5F18.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r18_nr_5F18 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_100 (s : N.State) (i : N.Inputs) :
  R.v100 (state s) (inputs i) = Zmod.unsigned (N.v100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v100 s i)) at 1.
  unfold R.v100, N.v100.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_101 (s : N.State) (i : N.Inputs) :
  R.v101 (state s) (inputs i) = Zmod.unsigned (N.v101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v101 s i)) at 1.
  unfold R.v101, N.v101.
  rewrite ?node_100.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r19_nr_5F19.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r19_nr_5F19 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_102 (s : N.State) (i : N.Inputs) :
  R.v102 (state s) (inputs i) = Zmod.unsigned (N.v102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v102 s i)) at 1.
  unfold R.v102, N.v102.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_103 (s : N.State) (i : N.Inputs) :
  R.v103 (state s) (inputs i) = Zmod.unsigned (N.v103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v103 s i)) at 1.
  unfold R.v103, N.v103.
  rewrite ?node_102.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r20_nr_5F20.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r20_nr_5F20 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_104 (s : N.State) (i : N.Inputs) :
  R.v104 (state s) (inputs i) = Zmod.unsigned (N.v104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v104 s i)) at 1.
  unfold R.v104, N.v104.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_105 (s : N.State) (i : N.Inputs) :
  R.v105 (state s) (inputs i) = Zmod.unsigned (N.v105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v105 s i)) at 1.
  unfold R.v105, N.v105.
  unfold R.v33, N.v33.
  rewrite ?node_104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_106 (s : N.State) (i : N.Inputs) :
  R.v106 (state s) (inputs i) = Zmod.unsigned (N.v106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v106 s i)) at 1.
  unfold R.v106, N.v106.
  unfold R.v35, N.v35.
  rewrite ?node_104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_107 (s : N.State) (i : N.Inputs) :
  R.v107 (state s) (inputs i) = Zmod.unsigned (N.v107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v107 s i)) at 1.
  unfold R.v107, N.v107.
  rewrite ?node_105.
  rewrite ?node_106.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_108 (s : N.State) (i : N.Inputs) :
  R.v108 (state s) (inputs i) = Zmod.unsigned (N.v108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v108 s i)) at 1.
  unfold R.v108, N.v108.
  unfold R.v39, N.v39.
  rewrite ?node_104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_109 (s : N.State) (i : N.Inputs) :
  R.v109 (state s) (inputs i) = Zmod.unsigned (N.v109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v109 s i)) at 1.
  unfold R.v109, N.v109.
  unfold R.v42, N.v42.
  rewrite ?node_104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_110 (s : N.State) (i : N.Inputs) :
  R.v110 (state s) (inputs i) = Zmod.unsigned (N.v110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v110 s i)) at 1.
  unfold R.v110, N.v110.
  unfold R.v45, N.v45.
  rewrite ?node_104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_111 (s : N.State) (i : N.Inputs) :
  R.v111 (state s) (inputs i) = Zmod.unsigned (N.v111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v111 s i)) at 1.
  unfold R.v111, N.v111.
  unfold R.v47, N.v47.
  rewrite ?node_104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_112 (s : N.State) (i : N.Inputs) :
  R.v112 (state s) (inputs i) = Zmod.unsigned (N.v112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v112 s i)) at 1.
  unfold R.v112, N.v112.
  rewrite ?node_110.
  rewrite ?node_111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_113 (s : N.State) (i : N.Inputs) :
  R.v113 (state s) (inputs i) = Zmod.unsigned (N.v113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v113 s i)) at 1.
  unfold R.v113, N.v113.
  unfold R.v11, N.v11.
  rewrite ?node_50.
  rewrite ?node_112.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_114 (s : N.State) (i : N.Inputs) :
  R.v114 (state s) (inputs i) = Zmod.unsigned (N.v114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v114 s i)) at 1.
  unfold R.v114, N.v114.
  rewrite ?node_44.
  rewrite ?node_109.
  rewrite ?node_113.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_115 (s : N.State) (i : N.Inputs) :
  R.v115 (state s) (inputs i) = Zmod.unsigned (N.v115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v115 s i)) at 1.
  unfold R.v115, N.v115.
  rewrite ?node_41.
  rewrite ?node_108.
  rewrite ?node_114.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_116 (s : N.State) (i : N.Inputs) :
  R.v116 (state s) (inputs i) = Zmod.unsigned (N.v116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v116 s i)) at 1.
  unfold R.v116, N.v116.
  rewrite ?node_38.
  rewrite ?node_107.
  rewrite ?node_115.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_117 (s : N.State) (i : N.Inputs) :
  R.v117 (state s) (inputs i) = Zmod.unsigned (N.v117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v117 s i)) at 1.
  unfold R.v117, N.v117.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_118 (s : N.State) (i : N.Inputs) :
  R.v118 (state s) (inputs i) = Zmod.unsigned (N.v118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v118 s i)) at 1.
  unfold R.v118, N.v118.
  rewrite ?node_117.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r21_nr_5F21.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r21_nr_5F21 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_119 (s : N.State) (i : N.Inputs) :
  R.v119 (state s) (inputs i) = Zmod.unsigned (N.v119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v119 s i)) at 1.
  unfold R.v119, N.v119.
  unfold R.v6, N.v6.
  rewrite ?node_108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_120 (s : N.State) (i : N.Inputs) :
  R.v120 (state s) (inputs i) = Zmod.unsigned (N.v120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v120 s i)) at 1.
  unfold R.v120, N.v120.
  unfold R.v19, N.v19.
  rewrite ?node_107.
  rewrite ?node_119.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_121 (s : N.State) (i : N.Inputs) :
  R.v121 (state s) (inputs i) = Zmod.unsigned (N.v121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v121 s i)) at 1.
  unfold R.v121, N.v121.
  rewrite ?node_120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_122 (s : N.State) (i : N.Inputs) :
  R.v122 (state s) (inputs i) = Zmod.unsigned (N.v122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v122 s i)) at 1.
  unfold R.v122, N.v122.
  rewrite ?node_121.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r22_nr_5F22.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r22_nr_5F22 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_123 (s : N.State) (i : N.Inputs) :
  R.v123 (state s) (inputs i) = Zmod.unsigned (N.v123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v123 s i)) at 1.
  unfold R.v123, N.v123.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_124 (s : N.State) (i : N.Inputs) :
  R.v124 (state s) (inputs i) = Zmod.unsigned (N.v124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v124 s i)) at 1.
  unfold R.v124, N.v124.
  rewrite ?node_123.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r23_nr_5F23.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r23_nr_5F23 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_125 (s : N.State) (i : N.Inputs) :
  R.v125 (state s) (inputs i) = Zmod.unsigned (N.v125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v125 s i)) at 1.
  unfold R.v125, N.v125.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_126 (s : N.State) (i : N.Inputs) :
  R.v126 (state s) (inputs i) = Zmod.unsigned (N.v126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v126 s i)) at 1.
  unfold R.v126, N.v126.
  rewrite ?node_125.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r24_nr_5F24.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r24_nr_5F24 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_127 (s : N.State) (i : N.Inputs) :
  R.v127 (state s) (inputs i) = Zmod.unsigned (N.v127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v127 s i)) at 1.
  unfold R.v127, N.v127.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_128 (s : N.State) (i : N.Inputs) :
  R.v128 (state s) (inputs i) = Zmod.unsigned (N.v128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v128 s i)) at 1.
  unfold R.v128, N.v128.
  rewrite ?node_127.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r25_nr_5F25.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r25_nr_5F25 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_129 (s : N.State) (i : N.Inputs) :
  R.v129 (state s) (inputs i) = Zmod.unsigned (N.v129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v129 s i)) at 1.
  unfold R.v129, N.v129.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_130 (s : N.State) (i : N.Inputs) :
  R.v130 (state s) (inputs i) = Zmod.unsigned (N.v130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v130 s i)) at 1.
  unfold R.v130, N.v130.
  rewrite ?node_129.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r26_nr_5F26.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r26_nr_5F26 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_131 (s : N.State) (i : N.Inputs) :
  R.v131 (state s) (inputs i) = Zmod.unsigned (N.v131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v131 s i)) at 1.
  unfold R.v131, N.v131.
  rewrite ?node_120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_132 (s : N.State) (i : N.Inputs) :
  R.v132 (state s) (inputs i) = Zmod.unsigned (N.v132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v132 s i)) at 1.
  unfold R.v132, N.v132.
  rewrite ?node_131.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r27_nr_5F27.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r27_nr_5F27 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_133 (s : N.State) (i : N.Inputs) :
  R.v133 (state s) (inputs i) = Zmod.unsigned (N.v133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v133 s i)) at 1.
  unfold R.v133, N.v133.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_134 (s : N.State) (i : N.Inputs) :
  R.v134 (state s) (inputs i) = Zmod.unsigned (N.v134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v134 s i)) at 1.
  unfold R.v134, N.v134.
  rewrite ?node_133.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r28_nr_5F28.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r28_nr_5F28 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_135 (s : N.State) (i : N.Inputs) :
  R.v135 (state s) (inputs i) = Zmod.unsigned (N.v135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v135 s i)) at 1.
  unfold R.v135, N.v135.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_136 (s : N.State) (i : N.Inputs) :
  R.v136 (state s) (inputs i) = Zmod.unsigned (N.v136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v136 s i)) at 1.
  unfold R.v136, N.v136.
  rewrite ?node_135.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r29_nr_5F29.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r29_nr_5F29 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_137 (s : N.State) (i : N.Inputs) :
  R.v137 (state s) (inputs i) = Zmod.unsigned (N.v137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v137 s i)) at 1.
  unfold R.v137, N.v137.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_138 (s : N.State) (i : N.Inputs) :
  R.v138 (state s) (inputs i) = Zmod.unsigned (N.v138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v138 s i)) at 1.
  unfold R.v138, N.v138.
  rewrite ?node_137.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r30_nr_5F30.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r30_nr_5F30 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_139 (s : N.State) (i : N.Inputs) :
  R.v139 (state s) (inputs i) = Zmod.unsigned (N.v139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v139 s i)) at 1.
  unfold R.v139, N.v139.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_140 (s : N.State) (i : N.Inputs) :
  R.v140 (state s) (inputs i) = Zmod.unsigned (N.v140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v140 s i)) at 1.
  unfold R.v140, N.v140.
  rewrite ?node_139.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r31_nr_5F31.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r31_nr_5F31 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_141 (s : N.State) (i : N.Inputs) :
  R.v141 (state s) (inputs i) = Zmod.unsigned (N.v141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v141 s i)) at 1.
  unfold R.v141, N.v141.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_142 (s : N.State) (i : N.Inputs) :
  R.v142 (state s) (inputs i) = Zmod.unsigned (N.v142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v142 s i)) at 1.
  unfold R.v142, N.v142.
  unfold R.v33, N.v33.
  rewrite ?node_141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_143 (s : N.State) (i : N.Inputs) :
  R.v143 (state s) (inputs i) = Zmod.unsigned (N.v143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v143 s i)) at 1.
  unfold R.v143, N.v143.
  unfold R.v35, N.v35.
  rewrite ?node_141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_144 (s : N.State) (i : N.Inputs) :
  R.v144 (state s) (inputs i) = Zmod.unsigned (N.v144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v144 s i)) at 1.
  unfold R.v144, N.v144.
  rewrite ?node_142.
  rewrite ?node_143.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_145 (s : N.State) (i : N.Inputs) :
  R.v145 (state s) (inputs i) = Zmod.unsigned (N.v145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v145 s i)) at 1.
  unfold R.v145, N.v145.
  unfold R.v39, N.v39.
  rewrite ?node_141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_146 (s : N.State) (i : N.Inputs) :
  R.v146 (state s) (inputs i) = Zmod.unsigned (N.v146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v146 s i)) at 1.
  unfold R.v146, N.v146.
  unfold R.v42, N.v42.
  rewrite ?node_141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_147 (s : N.State) (i : N.Inputs) :
  R.v147 (state s) (inputs i) = Zmod.unsigned (N.v147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v147 s i)) at 1.
  unfold R.v147, N.v147.
  unfold R.v45, N.v45.
  rewrite ?node_141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_148 (s : N.State) (i : N.Inputs) :
  R.v148 (state s) (inputs i) = Zmod.unsigned (N.v148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v148 s i)) at 1.
  unfold R.v148, N.v148.
  unfold R.v47, N.v47.
  rewrite ?node_141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_149 (s : N.State) (i : N.Inputs) :
  R.v149 (state s) (inputs i) = Zmod.unsigned (N.v149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v149 s i)) at 1.
  unfold R.v149, N.v149.
  rewrite ?node_147.
  rewrite ?node_148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_150 (s : N.State) (i : N.Inputs) :
  R.v150 (state s) (inputs i) = Zmod.unsigned (N.v150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v150 s i)) at 1.
  unfold R.v150, N.v150.
  unfold R.v11, N.v11.
  rewrite ?node_50.
  rewrite ?node_149.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_151 (s : N.State) (i : N.Inputs) :
  R.v151 (state s) (inputs i) = Zmod.unsigned (N.v151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v151 s i)) at 1.
  unfold R.v151, N.v151.
  rewrite ?node_44.
  rewrite ?node_146.
  rewrite ?node_150.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_152 (s : N.State) (i : N.Inputs) :
  R.v152 (state s) (inputs i) = Zmod.unsigned (N.v152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v152 s i)) at 1.
  unfold R.v152, N.v152.
  rewrite ?node_41.
  rewrite ?node_145.
  rewrite ?node_151.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_153 (s : N.State) (i : N.Inputs) :
  R.v153 (state s) (inputs i) = Zmod.unsigned (N.v153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v153 s i)) at 1.
  unfold R.v153, N.v153.
  rewrite ?node_38.
  rewrite ?node_144.
  rewrite ?node_152.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_154 (s : N.State) (i : N.Inputs) :
  R.v154 (state s) (inputs i) = Zmod.unsigned (N.v154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v154 s i)) at 1.
  unfold R.v154, N.v154.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_155 (s : N.State) (i : N.Inputs) :
  R.v155 (state s) (inputs i) = Zmod.unsigned (N.v155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v155 s i)) at 1.
  unfold R.v155, N.v155.
  rewrite ?node_154.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r32_nr_5F32.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r32_nr_5F32 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_156 (s : N.State) (i : N.Inputs) :
  R.v156 (state s) (inputs i) = Zmod.unsigned (N.v156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v156 s i)) at 1.
  unfold R.v156, N.v156.
  unfold R.v6, N.v6.
  rewrite ?node_145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_157 (s : N.State) (i : N.Inputs) :
  R.v157 (state s) (inputs i) = Zmod.unsigned (N.v157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v157 s i)) at 1.
  unfold R.v157, N.v157.
  unfold R.v19, N.v19.
  rewrite ?node_144.
  rewrite ?node_156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_158 (s : N.State) (i : N.Inputs) :
  R.v158 (state s) (inputs i) = Zmod.unsigned (N.v158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v158 s i)) at 1.
  unfold R.v158, N.v158.
  rewrite ?node_157.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_159 (s : N.State) (i : N.Inputs) :
  R.v159 (state s) (inputs i) = Zmod.unsigned (N.v159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v159 s i)) at 1.
  unfold R.v159, N.v159.
  rewrite ?node_158.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r33_nr_5F33.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r33_nr_5F33 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_160 (s : N.State) (i : N.Inputs) :
  R.v160 (state s) (inputs i) = Zmod.unsigned (N.v160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v160 s i)) at 1.
  unfold R.v160, N.v160.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_161 (s : N.State) (i : N.Inputs) :
  R.v161 (state s) (inputs i) = Zmod.unsigned (N.v161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v161 s i)) at 1.
  unfold R.v161, N.v161.
  rewrite ?node_160.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r34_nr_5F34.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r34_nr_5F34 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_162 (s : N.State) (i : N.Inputs) :
  R.v162 (state s) (inputs i) = Zmod.unsigned (N.v162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v162 s i)) at 1.
  unfold R.v162, N.v162.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_163 (s : N.State) (i : N.Inputs) :
  R.v163 (state s) (inputs i) = Zmod.unsigned (N.v163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v163 s i)) at 1.
  unfold R.v163, N.v163.
  rewrite ?node_162.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r35_nr_5F35.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r35_nr_5F35 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_164 (s : N.State) (i : N.Inputs) :
  R.v164 (state s) (inputs i) = Zmod.unsigned (N.v164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v164 s i)) at 1.
  unfold R.v164, N.v164.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_165 (s : N.State) (i : N.Inputs) :
  R.v165 (state s) (inputs i) = Zmod.unsigned (N.v165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v165 s i)) at 1.
  unfold R.v165, N.v165.
  rewrite ?node_164.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r36_nr_5F36.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r36_nr_5F36 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_166 (s : N.State) (i : N.Inputs) :
  R.v166 (state s) (inputs i) = Zmod.unsigned (N.v166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v166 s i)) at 1.
  unfold R.v166, N.v166.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_167 (s : N.State) (i : N.Inputs) :
  R.v167 (state s) (inputs i) = Zmod.unsigned (N.v167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v167 s i)) at 1.
  unfold R.v167, N.v167.
  rewrite ?node_166.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r37_nr_5F37.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r37_nr_5F37 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_168 (s : N.State) (i : N.Inputs) :
  R.v168 (state s) (inputs i) = Zmod.unsigned (N.v168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v168 s i)) at 1.
  unfold R.v168, N.v168.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_169 (s : N.State) (i : N.Inputs) :
  R.v169 (state s) (inputs i) = Zmod.unsigned (N.v169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v169 s i)) at 1.
  unfold R.v169, N.v169.
  rewrite ?node_168.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r38_nr_5F38.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r38_nr_5F38 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_170 (s : N.State) (i : N.Inputs) :
  R.v170 (state s) (inputs i) = Zmod.unsigned (N.v170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v170 s i)) at 1.
  unfold R.v170, N.v170.
  rewrite ?node_157.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_171 (s : N.State) (i : N.Inputs) :
  R.v171 (state s) (inputs i) = Zmod.unsigned (N.v171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v171 s i)) at 1.
  unfold R.v171, N.v171.
  rewrite ?node_170.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r39_nr_5F39.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r39_nr_5F39 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_172 (s : N.State) (i : N.Inputs) :
  R.v172 (state s) (inputs i) = Zmod.unsigned (N.v172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v172 s i)) at 1.
  unfold R.v172, N.v172.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_173 (s : N.State) (i : N.Inputs) :
  R.v173 (state s) (inputs i) = Zmod.unsigned (N.v173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v173 s i)) at 1.
  unfold R.v173, N.v173.
  rewrite ?node_172.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r40_nr_5F40.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r40_nr_5F40 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_174 (s : N.State) (i : N.Inputs) :
  R.v174 (state s) (inputs i) = Zmod.unsigned (N.v174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v174 s i)) at 1.
  unfold R.v174, N.v174.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_175 (s : N.State) (i : N.Inputs) :
  R.v175 (state s) (inputs i) = Zmod.unsigned (N.v175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v175 s i)) at 1.
  unfold R.v175, N.v175.
  rewrite ?node_174.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r41_nr_5F41.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r41_nr_5F41 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_176 (s : N.State) (i : N.Inputs) :
  R.v176 (state s) (inputs i) = Zmod.unsigned (N.v176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v176 s i)) at 1.
  unfold R.v176, N.v176.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_177 (s : N.State) (i : N.Inputs) :
  R.v177 (state s) (inputs i) = Zmod.unsigned (N.v177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v177 s i)) at 1.
  unfold R.v177, N.v177.
  rewrite ?node_176.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r42_nr_5F42.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r42_nr_5F42 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_178 (s : N.State) (i : N.Inputs) :
  R.v178 (state s) (inputs i) = Zmod.unsigned (N.v178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v178 s i)) at 1.
  unfold R.v178, N.v178.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_179 (s : N.State) (i : N.Inputs) :
  R.v179 (state s) (inputs i) = Zmod.unsigned (N.v179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v179 s i)) at 1.
  unfold R.v179, N.v179.
  rewrite ?node_178.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r43_nr_5F43.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r43_nr_5F43 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_180 (s : N.State) (i : N.Inputs) :
  R.v180 (state s) (inputs i) = Zmod.unsigned (N.v180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v180 s i)) at 1.
  unfold R.v180, N.v180.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_181 (s : N.State) (i : N.Inputs) :
  R.v181 (state s) (inputs i) = Zmod.unsigned (N.v181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v181 s i)) at 1.
  unfold R.v181, N.v181.
  rewrite ?node_180.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r44_nr_5F44.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r44_nr_5F44 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_182 (s : N.State) (i : N.Inputs) :
  R.v182 (state s) (inputs i) = Zmod.unsigned (N.v182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v182 s i)) at 1.
  unfold R.v182, N.v182.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_183 (s : N.State) (i : N.Inputs) :
  R.v183 (state s) (inputs i) = Zmod.unsigned (N.v183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v183 s i)) at 1.
  unfold R.v183, N.v183.
  unfold R.v33, N.v33.
  rewrite ?node_182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_184 (s : N.State) (i : N.Inputs) :
  R.v184 (state s) (inputs i) = Zmod.unsigned (N.v184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v184 s i)) at 1.
  unfold R.v184, N.v184.
  unfold R.v35, N.v35.
  rewrite ?node_182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_185 (s : N.State) (i : N.Inputs) :
  R.v185 (state s) (inputs i) = Zmod.unsigned (N.v185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v185 s i)) at 1.
  unfold R.v185, N.v185.
  rewrite ?node_183.
  rewrite ?node_184.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_186 (s : N.State) (i : N.Inputs) :
  R.v186 (state s) (inputs i) = Zmod.unsigned (N.v186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v186 s i)) at 1.
  unfold R.v186, N.v186.
  unfold R.v39, N.v39.
  rewrite ?node_182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_187 (s : N.State) (i : N.Inputs) :
  R.v187 (state s) (inputs i) = Zmod.unsigned (N.v187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v187 s i)) at 1.
  unfold R.v187, N.v187.
  unfold R.v42, N.v42.
  rewrite ?node_182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_188 (s : N.State) (i : N.Inputs) :
  R.v188 (state s) (inputs i) = Zmod.unsigned (N.v188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v188 s i)) at 1.
  unfold R.v188, N.v188.
  unfold R.v45, N.v45.
  rewrite ?node_182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_189 (s : N.State) (i : N.Inputs) :
  R.v189 (state s) (inputs i) = Zmod.unsigned (N.v189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v189 s i)) at 1.
  unfold R.v189, N.v189.
  unfold R.v47, N.v47.
  rewrite ?node_182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_190 (s : N.State) (i : N.Inputs) :
  R.v190 (state s) (inputs i) = Zmod.unsigned (N.v190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v190 s i)) at 1.
  unfold R.v190, N.v190.
  rewrite ?node_188.
  rewrite ?node_189.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_191 (s : N.State) (i : N.Inputs) :
  R.v191 (state s) (inputs i) = Zmod.unsigned (N.v191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v191 s i)) at 1.
  unfold R.v191, N.v191.
  unfold R.v11, N.v11.
  rewrite ?node_50.
  rewrite ?node_190.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_192 (s : N.State) (i : N.Inputs) :
  R.v192 (state s) (inputs i) = Zmod.unsigned (N.v192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v192 s i)) at 1.
  unfold R.v192, N.v192.
  rewrite ?node_44.
  rewrite ?node_187.
  rewrite ?node_191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_193 (s : N.State) (i : N.Inputs) :
  R.v193 (state s) (inputs i) = Zmod.unsigned (N.v193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v193 s i)) at 1.
  unfold R.v193, N.v193.
  rewrite ?node_41.
  rewrite ?node_186.
  rewrite ?node_192.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_194 (s : N.State) (i : N.Inputs) :
  R.v194 (state s) (inputs i) = Zmod.unsigned (N.v194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v194 s i)) at 1.
  unfold R.v194, N.v194.
  rewrite ?node_38.
  rewrite ?node_185.
  rewrite ?node_193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_195 (s : N.State) (i : N.Inputs) :
  R.v195 (state s) (inputs i) = Zmod.unsigned (N.v195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v195 s i)) at 1.
  unfold R.v195, N.v195.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_196 (s : N.State) (i : N.Inputs) :
  R.v196 (state s) (inputs i) = Zmod.unsigned (N.v196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v196 s i)) at 1.
  unfold R.v196, N.v196.
  rewrite ?node_195.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r45_nr_5F45.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r45_nr_5F45 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_197 (s : N.State) (i : N.Inputs) :
  R.v197 (state s) (inputs i) = Zmod.unsigned (N.v197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v197 s i)) at 1.
  unfold R.v197, N.v197.
  unfold R.v6, N.v6.
  rewrite ?node_186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_198 (s : N.State) (i : N.Inputs) :
  R.v198 (state s) (inputs i) = Zmod.unsigned (N.v198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v198 s i)) at 1.
  unfold R.v198, N.v198.
  unfold R.v19, N.v19.
  rewrite ?node_185.
  rewrite ?node_197.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_199 (s : N.State) (i : N.Inputs) :
  R.v199 (state s) (inputs i) = Zmod.unsigned (N.v199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v199 s i)) at 1.
  unfold R.v199, N.v199.
  rewrite ?node_198.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_200 (s : N.State) (i : N.Inputs) :
  R.v200 (state s) (inputs i) = Zmod.unsigned (N.v200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v200 s i)) at 1.
  unfold R.v200, N.v200.
  rewrite ?node_199.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r46_nr_5F46.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r46_nr_5F46 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_201 (s : N.State) (i : N.Inputs) :
  R.v201 (state s) (inputs i) = Zmod.unsigned (N.v201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v201 s i)) at 1.
  unfold R.v201, N.v201.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_202 (s : N.State) (i : N.Inputs) :
  R.v202 (state s) (inputs i) = Zmod.unsigned (N.v202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v202 s i)) at 1.
  unfold R.v202, N.v202.
  rewrite ?node_201.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r47_nr_5F47.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r47_nr_5F47 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_203 (s : N.State) (i : N.Inputs) :
  R.v203 (state s) (inputs i) = Zmod.unsigned (N.v203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v203 s i)) at 1.
  unfold R.v203, N.v203.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_204 (s : N.State) (i : N.Inputs) :
  R.v204 (state s) (inputs i) = Zmod.unsigned (N.v204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v204 s i)) at 1.
  unfold R.v204, N.v204.
  rewrite ?node_203.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r48_nr_5F48.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r48_nr_5F48 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_205 (s : N.State) (i : N.Inputs) :
  R.v205 (state s) (inputs i) = Zmod.unsigned (N.v205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v205 s i)) at 1.
  unfold R.v205, N.v205.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_206 (s : N.State) (i : N.Inputs) :
  R.v206 (state s) (inputs i) = Zmod.unsigned (N.v206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v206 s i)) at 1.
  unfold R.v206, N.v206.
  rewrite ?node_205.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r49_nr_5F49.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r49_nr_5F49 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_207 (s : N.State) (i : N.Inputs) :
  R.v207 (state s) (inputs i) = Zmod.unsigned (N.v207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v207 s i)) at 1.
  unfold R.v207, N.v207.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_208 (s : N.State) (i : N.Inputs) :
  R.v208 (state s) (inputs i) = Zmod.unsigned (N.v208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v208 s i)) at 1.
  unfold R.v208, N.v208.
  rewrite ?node_207.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r50_nr_5F50.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r50_nr_5F50 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_209 (s : N.State) (i : N.Inputs) :
  R.v209 (state s) (inputs i) = Zmod.unsigned (N.v209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v209 s i)) at 1.
  unfold R.v209, N.v209.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_210 (s : N.State) (i : N.Inputs) :
  R.v210 (state s) (inputs i) = Zmod.unsigned (N.v210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v210 s i)) at 1.
  unfold R.v210, N.v210.
  rewrite ?node_209.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r51_nr_5F51.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r51_nr_5F51 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_211 (s : N.State) (i : N.Inputs) :
  R.v211 (state s) (inputs i) = Zmod.unsigned (N.v211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v211 s i)) at 1.
  unfold R.v211, N.v211.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_212 (s : N.State) (i : N.Inputs) :
  R.v212 (state s) (inputs i) = Zmod.unsigned (N.v212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v212 s i)) at 1.
  unfold R.v212, N.v212.
  rewrite ?node_211.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r52_nr_5F52.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r52_nr_5F52 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_213 (s : N.State) (i : N.Inputs) :
  R.v213 (state s) (inputs i) = Zmod.unsigned (N.v213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v213 s i)) at 1.
  unfold R.v213, N.v213.
  rewrite ?node_198.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_214 (s : N.State) (i : N.Inputs) :
  R.v214 (state s) (inputs i) = Zmod.unsigned (N.v214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v214 s i)) at 1.
  unfold R.v214, N.v214.
  rewrite ?node_213.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r53_nr_5F53.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r53_nr_5F53 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_215 (s : N.State) (i : N.Inputs) :
  R.v215 (state s) (inputs i) = Zmod.unsigned (N.v215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v215 s i)) at 1.
  unfold R.v215, N.v215.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_216 (s : N.State) (i : N.Inputs) :
  R.v216 (state s) (inputs i) = Zmod.unsigned (N.v216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v216 s i)) at 1.
  unfold R.v216, N.v216.
  rewrite ?node_215.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r54_nr_5F54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r54_nr_5F54 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_217 (s : N.State) (i : N.Inputs) :
  R.v217 (state s) (inputs i) = Zmod.unsigned (N.v217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v217 s i)) at 1.
  unfold R.v217, N.v217.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_218 (s : N.State) (i : N.Inputs) :
  R.v218 (state s) (inputs i) = Zmod.unsigned (N.v218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v218 s i)) at 1.
  unfold R.v218, N.v218.
  rewrite ?node_217.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r55_nr_5F55.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r55_nr_5F55 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_219 (s : N.State) (i : N.Inputs) :
  R.v219 (state s) (inputs i) = Zmod.unsigned (N.v219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v219 s i)) at 1.
  unfold R.v219, N.v219.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_220 (s : N.State) (i : N.Inputs) :
  R.v220 (state s) (inputs i) = Zmod.unsigned (N.v220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v220 s i)) at 1.
  unfold R.v220, N.v220.
  rewrite ?node_219.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r56_nr_5F56.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r56_nr_5F56 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_221 (s : N.State) (i : N.Inputs) :
  R.v221 (state s) (inputs i) = Zmod.unsigned (N.v221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v221 s i)) at 1.
  unfold R.v221, N.v221.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_222 (s : N.State) (i : N.Inputs) :
  R.v222 (state s) (inputs i) = Zmod.unsigned (N.v222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v222 s i)) at 1.
  unfold R.v222, N.v222.
  rewrite ?node_221.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r57_nr_5F57.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r57_nr_5F57 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_223 (s : N.State) (i : N.Inputs) :
  R.v223 (state s) (inputs i) = Zmod.unsigned (N.v223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v223 s i)) at 1.
  unfold R.v223, N.v223.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_224 (s : N.State) (i : N.Inputs) :
  R.v224 (state s) (inputs i) = Zmod.unsigned (N.v224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v224 s i)) at 1.
  unfold R.v224, N.v224.
  rewrite ?node_223.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r58_nr_5F58.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r58_nr_5F58 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_225 (s : N.State) (i : N.Inputs) :
  R.v225 (state s) (inputs i) = Zmod.unsigned (N.v225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v225 s i)) at 1.
  unfold R.v225, N.v225.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_226 (s : N.State) (i : N.Inputs) :
  R.v226 (state s) (inputs i) = Zmod.unsigned (N.v226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v226 s i)) at 1.
  unfold R.v226, N.v226.
  rewrite ?node_225.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r59_nr_5F59.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r59_nr_5F59 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_227 (s : N.State) (i : N.Inputs) :
  R.v227 (state s) (inputs i) = Zmod.unsigned (N.v227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v227 s i)) at 1.
  unfold R.v227, N.v227.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_228 (s : N.State) (i : N.Inputs) :
  R.v228 (state s) (inputs i) = Zmod.unsigned (N.v228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v228 s i)) at 1.
  unfold R.v228, N.v228.
  unfold R.v33, N.v33.
  rewrite ?node_227.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_229 (s : N.State) (i : N.Inputs) :
  R.v229 (state s) (inputs i) = Zmod.unsigned (N.v229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v229 s i)) at 1.
  unfold R.v229, N.v229.
  unfold R.v35, N.v35.
  rewrite ?node_227.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_230 (s : N.State) (i : N.Inputs) :
  R.v230 (state s) (inputs i) = Zmod.unsigned (N.v230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v230 s i)) at 1.
  unfold R.v230, N.v230.
  rewrite ?node_228.
  rewrite ?node_229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_231 (s : N.State) (i : N.Inputs) :
  R.v231 (state s) (inputs i) = Zmod.unsigned (N.v231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v231 s i)) at 1.
  unfold R.v231, N.v231.
  unfold R.v39, N.v39.
  rewrite ?node_227.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_232 (s : N.State) (i : N.Inputs) :
  R.v232 (state s) (inputs i) = Zmod.unsigned (N.v232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v232 s i)) at 1.
  unfold R.v232, N.v232.
  unfold R.v42, N.v42.
  rewrite ?node_227.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_233 (s : N.State) (i : N.Inputs) :
  R.v233 (state s) (inputs i) = Zmod.unsigned (N.v233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v233 s i)) at 1.
  unfold R.v233, N.v233.
  unfold R.v45, N.v45.
  rewrite ?node_227.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_234 (s : N.State) (i : N.Inputs) :
  R.v234 (state s) (inputs i) = Zmod.unsigned (N.v234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v234 s i)) at 1.
  unfold R.v234, N.v234.
  unfold R.v47, N.v47.
  rewrite ?node_227.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_235 (s : N.State) (i : N.Inputs) :
  R.v235 (state s) (inputs i) = Zmod.unsigned (N.v235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v235 s i)) at 1.
  unfold R.v235, N.v235.
  rewrite ?node_233.
  rewrite ?node_234.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_236 (s : N.State) (i : N.Inputs) :
  R.v236 (state s) (inputs i) = Zmod.unsigned (N.v236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v236 s i)) at 1.
  unfold R.v236, N.v236.
  unfold R.v11, N.v11.
  rewrite ?node_50.
  rewrite ?node_235.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_237 (s : N.State) (i : N.Inputs) :
  R.v237 (state s) (inputs i) = Zmod.unsigned (N.v237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v237 s i)) at 1.
  unfold R.v237, N.v237.
  rewrite ?node_44.
  rewrite ?node_232.
  rewrite ?node_236.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_238 (s : N.State) (i : N.Inputs) :
  R.v238 (state s) (inputs i) = Zmod.unsigned (N.v238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v238 s i)) at 1.
  unfold R.v238, N.v238.
  rewrite ?node_41.
  rewrite ?node_231.
  rewrite ?node_237.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_239 (s : N.State) (i : N.Inputs) :
  R.v239 (state s) (inputs i) = Zmod.unsigned (N.v239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v239 s i)) at 1.
  unfold R.v239, N.v239.
  rewrite ?node_38.
  rewrite ?node_230.
  rewrite ?node_238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_240 (s : N.State) (i : N.Inputs) :
  R.v240 (state s) (inputs i) = Zmod.unsigned (N.v240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v240 s i)) at 1.
  unfold R.v240, N.v240.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_241 (s : N.State) (i : N.Inputs) :
  R.v241 (state s) (inputs i) = Zmod.unsigned (N.v241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v241 s i)) at 1.
  unfold R.v241, N.v241.
  rewrite ?node_240.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r60_nr_5F60.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r60_nr_5F60 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_242 (s : N.State) (i : N.Inputs) :
  R.v242 (state s) (inputs i) = Zmod.unsigned (N.v242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v242 s i)) at 1.
  unfold R.v242, N.v242.
  unfold R.v6, N.v6.
  rewrite ?node_231.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_243 (s : N.State) (i : N.Inputs) :
  R.v243 (state s) (inputs i) = Zmod.unsigned (N.v243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v243 s i)) at 1.
  unfold R.v243, N.v243.
  unfold R.v19, N.v19.
  rewrite ?node_230.
  rewrite ?node_242.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_244 (s : N.State) (i : N.Inputs) :
  R.v244 (state s) (inputs i) = Zmod.unsigned (N.v244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v244 s i)) at 1.
  unfold R.v244, N.v244.
  rewrite ?node_243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_245 (s : N.State) (i : N.Inputs) :
  R.v245 (state s) (inputs i) = Zmod.unsigned (N.v245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v245 s i)) at 1.
  unfold R.v245, N.v245.
  rewrite ?node_244.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r61_nr_5F61.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r61_nr_5F61 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_246 (s : N.State) (i : N.Inputs) :
  R.v246 (state s) (inputs i) = Zmod.unsigned (N.v246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v246 s i)) at 1.
  unfold R.v246, N.v246.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_247 (s : N.State) (i : N.Inputs) :
  R.v247 (state s) (inputs i) = Zmod.unsigned (N.v247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v247 s i)) at 1.
  unfold R.v247, N.v247.
  rewrite ?node_246.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r62_nr_5F62.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r62_nr_5F62 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_248 (s : N.State) (i : N.Inputs) :
  R.v248 (state s) (inputs i) = Zmod.unsigned (N.v248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v248 s i)) at 1.
  unfold R.v248, N.v248.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_249 (s : N.State) (i : N.Inputs) :
  R.v249 (state s) (inputs i) = Zmod.unsigned (N.v249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v249 s i)) at 1.
  unfold R.v249, N.v249.
  rewrite ?node_248.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r63_nr_5F63.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r63_nr_5F63 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_250 (s : N.State) (i : N.Inputs) :
  R.v250 (state s) (inputs i) = Zmod.unsigned (N.v250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v250 s i)) at 1.
  unfold R.v250, N.v250.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_251 (s : N.State) (i : N.Inputs) :
  R.v251 (state s) (inputs i) = Zmod.unsigned (N.v251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v251 s i)) at 1.
  unfold R.v251, N.v251.
  rewrite ?node_250.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r64_nr_5F64.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r64_nr_5F64 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_252 (s : N.State) (i : N.Inputs) :
  R.v252 (state s) (inputs i) = Zmod.unsigned (N.v252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v252 s i)) at 1.
  unfold R.v252, N.v252.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_253 (s : N.State) (i : N.Inputs) :
  R.v253 (state s) (inputs i) = Zmod.unsigned (N.v253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v253 s i)) at 1.
  unfold R.v253, N.v253.
  rewrite ?node_252.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r65_nr_5F65.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r65_nr_5F65 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_254 (s : N.State) (i : N.Inputs) :
  R.v254 (state s) (inputs i) = Zmod.unsigned (N.v254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v254 s i)) at 1.
  unfold R.v254, N.v254.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_255 (s : N.State) (i : N.Inputs) :
  R.v255 (state s) (inputs i) = Zmod.unsigned (N.v255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v255 s i)) at 1.
  unfold R.v255, N.v255.
  rewrite ?node_254.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r66_nr_5F66.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r66_nr_5F66 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_256 (s : N.State) (i : N.Inputs) :
  R.v256 (state s) (inputs i) = Zmod.unsigned (N.v256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v256 s i)) at 1.
  unfold R.v256, N.v256.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_257 (s : N.State) (i : N.Inputs) :
  R.v257 (state s) (inputs i) = Zmod.unsigned (N.v257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v257 s i)) at 1.
  unfold R.v257, N.v257.
  rewrite ?node_256.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r67_nr_5F67.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r67_nr_5F67 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_258 (s : N.State) (i : N.Inputs) :
  R.v258 (state s) (inputs i) = Zmod.unsigned (N.v258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v258 s i)) at 1.
  unfold R.v258, N.v258.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_259 (s : N.State) (i : N.Inputs) :
  R.v259 (state s) (inputs i) = Zmod.unsigned (N.v259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v259 s i)) at 1.
  unfold R.v259, N.v259.
  rewrite ?node_258.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r68_nr_5F68.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r68_nr_5F68 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_260 (s : N.State) (i : N.Inputs) :
  R.v260 (state s) (inputs i) = Zmod.unsigned (N.v260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v260 s i)) at 1.
  unfold R.v260, N.v260.
  rewrite ?node_243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_261 (s : N.State) (i : N.Inputs) :
  R.v261 (state s) (inputs i) = Zmod.unsigned (N.v261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v261 s i)) at 1.
  unfold R.v261, N.v261.
  rewrite ?node_260.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r69_nr_5F69.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r69_nr_5F69 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_262 (s : N.State) (i : N.Inputs) :
  R.v262 (state s) (inputs i) = Zmod.unsigned (N.v262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v262 s i)) at 1.
  unfold R.v262, N.v262.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_263 (s : N.State) (i : N.Inputs) :
  R.v263 (state s) (inputs i) = Zmod.unsigned (N.v263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v263 s i)) at 1.
  unfold R.v263, N.v263.
  rewrite ?node_262.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r70_nr_5F70.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r70_nr_5F70 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_264 (s : N.State) (i : N.Inputs) :
  R.v264 (state s) (inputs i) = Zmod.unsigned (N.v264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v264 s i)) at 1.
  unfold R.v264, N.v264.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_265 (s : N.State) (i : N.Inputs) :
  R.v265 (state s) (inputs i) = Zmod.unsigned (N.v265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v265 s i)) at 1.
  unfold R.v265, N.v265.
  rewrite ?node_264.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r71_nr_5F71.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r71_nr_5F71 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_266 (s : N.State) (i : N.Inputs) :
  R.v266 (state s) (inputs i) = Zmod.unsigned (N.v266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v266 s i)) at 1.
  unfold R.v266, N.v266.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_267 (s : N.State) (i : N.Inputs) :
  R.v267 (state s) (inputs i) = Zmod.unsigned (N.v267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v267 s i)) at 1.
  unfold R.v267, N.v267.
  rewrite ?node_266.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r72_nr_5F72.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r72_nr_5F72 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_268 (s : N.State) (i : N.Inputs) :
  R.v268 (state s) (inputs i) = Zmod.unsigned (N.v268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v268 s i)) at 1.
  unfold R.v268, N.v268.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_269 (s : N.State) (i : N.Inputs) :
  R.v269 (state s) (inputs i) = Zmod.unsigned (N.v269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v269 s i)) at 1.
  unfold R.v269, N.v269.
  rewrite ?node_268.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r73_nr_5F73.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r73_nr_5F73 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_270 (s : N.State) (i : N.Inputs) :
  R.v270 (state s) (inputs i) = Zmod.unsigned (N.v270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v270 s i)) at 1.
  unfold R.v270, N.v270.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_271 (s : N.State) (i : N.Inputs) :
  R.v271 (state s) (inputs i) = Zmod.unsigned (N.v271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v271 s i)) at 1.
  unfold R.v271, N.v271.
  rewrite ?node_270.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r74_nr_5F74.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r74_nr_5F74 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_272 (s : N.State) (i : N.Inputs) :
  R.v272 (state s) (inputs i) = Zmod.unsigned (N.v272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v272 s i)) at 1.
  unfold R.v272, N.v272.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_273 (s : N.State) (i : N.Inputs) :
  R.v273 (state s) (inputs i) = Zmod.unsigned (N.v273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v273 s i)) at 1.
  unfold R.v273, N.v273.
  rewrite ?node_272.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r75_nr_5F75.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r75_nr_5F75 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_274 (s : N.State) (i : N.Inputs) :
  R.v274 (state s) (inputs i) = Zmod.unsigned (N.v274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v274 s i)) at 1.
  unfold R.v274, N.v274.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_275 (s : N.State) (i : N.Inputs) :
  R.v275 (state s) (inputs i) = Zmod.unsigned (N.v275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v275 s i)) at 1.
  unfold R.v275, N.v275.
  rewrite ?node_274.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r76_nr_5F76.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r76_nr_5F76 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_276 (s : N.State) (i : N.Inputs) :
  R.v276 (state s) (inputs i) = Zmod.unsigned (N.v276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v276 s i)) at 1.
  unfold R.v276, N.v276.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_277 (s : N.State) (i : N.Inputs) :
  R.v277 (state s) (inputs i) = Zmod.unsigned (N.v277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v277 s i)) at 1.
  unfold R.v277, N.v277.
  unfold R.v33, N.v33.
  rewrite ?node_276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_278 (s : N.State) (i : N.Inputs) :
  R.v278 (state s) (inputs i) = Zmod.unsigned (N.v278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v278 s i)) at 1.
  unfold R.v278, N.v278.
  unfold R.v35, N.v35.
  rewrite ?node_276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_279 (s : N.State) (i : N.Inputs) :
  R.v279 (state s) (inputs i) = Zmod.unsigned (N.v279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v279 s i)) at 1.
  unfold R.v279, N.v279.
  rewrite ?node_277.
  rewrite ?node_278.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_280 (s : N.State) (i : N.Inputs) :
  R.v280 (state s) (inputs i) = Zmod.unsigned (N.v280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v280 s i)) at 1.
  unfold R.v280, N.v280.
  unfold R.v39, N.v39.
  rewrite ?node_276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_281 (s : N.State) (i : N.Inputs) :
  R.v281 (state s) (inputs i) = Zmod.unsigned (N.v281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v281 s i)) at 1.
  unfold R.v281, N.v281.
  unfold R.v42, N.v42.
  rewrite ?node_276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_282 (s : N.State) (i : N.Inputs) :
  R.v282 (state s) (inputs i) = Zmod.unsigned (N.v282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v282 s i)) at 1.
  unfold R.v282, N.v282.
  unfold R.v45, N.v45.
  rewrite ?node_276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_283 (s : N.State) (i : N.Inputs) :
  R.v283 (state s) (inputs i) = Zmod.unsigned (N.v283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v283 s i)) at 1.
  unfold R.v283, N.v283.
  unfold R.v47, N.v47.
  rewrite ?node_276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_284 (s : N.State) (i : N.Inputs) :
  R.v284 (state s) (inputs i) = Zmod.unsigned (N.v284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v284 s i)) at 1.
  unfold R.v284, N.v284.
  rewrite ?node_282.
  rewrite ?node_283.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_285 (s : N.State) (i : N.Inputs) :
  R.v285 (state s) (inputs i) = Zmod.unsigned (N.v285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v285 s i)) at 1.
  unfold R.v285, N.v285.
  unfold R.v11, N.v11.
  rewrite ?node_50.
  rewrite ?node_284.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_286 (s : N.State) (i : N.Inputs) :
  R.v286 (state s) (inputs i) = Zmod.unsigned (N.v286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v286 s i)) at 1.
  unfold R.v286, N.v286.
  rewrite ?node_44.
  rewrite ?node_281.
  rewrite ?node_285.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_287 (s : N.State) (i : N.Inputs) :
  R.v287 (state s) (inputs i) = Zmod.unsigned (N.v287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v287 s i)) at 1.
  unfold R.v287, N.v287.
  rewrite ?node_41.
  rewrite ?node_280.
  rewrite ?node_286.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_288 (s : N.State) (i : N.Inputs) :
  R.v288 (state s) (inputs i) = Zmod.unsigned (N.v288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v288 s i)) at 1.
  unfold R.v288, N.v288.
  rewrite ?node_38.
  rewrite ?node_279.
  rewrite ?node_287.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_289 (s : N.State) (i : N.Inputs) :
  R.v289 (state s) (inputs i) = Zmod.unsigned (N.v289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v289 s i)) at 1.
  unfold R.v289, N.v289.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_290 (s : N.State) (i : N.Inputs) :
  R.v290 (state s) (inputs i) = Zmod.unsigned (N.v290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v290 s i)) at 1.
  unfold R.v290, N.v290.
  rewrite ?node_289.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r77_nr_5F77.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r77_nr_5F77 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_291 (s : N.State) (i : N.Inputs) :
  R.v291 (state s) (inputs i) = Zmod.unsigned (N.v291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v291 s i)) at 1.
  unfold R.v291, N.v291.
  unfold R.v6, N.v6.
  rewrite ?node_280.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_292 (s : N.State) (i : N.Inputs) :
  R.v292 (state s) (inputs i) = Zmod.unsigned (N.v292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v292 s i)) at 1.
  unfold R.v292, N.v292.
  unfold R.v19, N.v19.
  rewrite ?node_279.
  rewrite ?node_291.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_293 (s : N.State) (i : N.Inputs) :
  R.v293 (state s) (inputs i) = Zmod.unsigned (N.v293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v293 s i)) at 1.
  unfold R.v293, N.v293.
  rewrite ?node_292.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_294 (s : N.State) (i : N.Inputs) :
  R.v294 (state s) (inputs i) = Zmod.unsigned (N.v294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v294 s i)) at 1.
  unfold R.v294, N.v294.
  rewrite ?node_293.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r78_nr_5F78.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r78_nr_5F78 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_295 (s : N.State) (i : N.Inputs) :
  R.v295 (state s) (inputs i) = Zmod.unsigned (N.v295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v295 s i)) at 1.
  unfold R.v295, N.v295.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_296 (s : N.State) (i : N.Inputs) :
  R.v296 (state s) (inputs i) = Zmod.unsigned (N.v296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v296 s i)) at 1.
  unfold R.v296, N.v296.
  rewrite ?node_295.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r79_nr_5F79.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r79_nr_5F79 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_297 (s : N.State) (i : N.Inputs) :
  R.v297 (state s) (inputs i) = Zmod.unsigned (N.v297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v297 s i)) at 1.
  unfold R.v297, N.v297.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_298 (s : N.State) (i : N.Inputs) :
  R.v298 (state s) (inputs i) = Zmod.unsigned (N.v298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v298 s i)) at 1.
  unfold R.v298, N.v298.
  rewrite ?node_297.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r80_nr_5F80.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r80_nr_5F80 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_299 (s : N.State) (i : N.Inputs) :
  R.v299 (state s) (inputs i) = Zmod.unsigned (N.v299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v299 s i)) at 1.
  unfold R.v299, N.v299.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_300 (s : N.State) (i : N.Inputs) :
  R.v300 (state s) (inputs i) = Zmod.unsigned (N.v300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v300 s i)) at 1.
  unfold R.v300, N.v300.
  rewrite ?node_299.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r81_nr_5F81.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r81_nr_5F81 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_301 (s : N.State) (i : N.Inputs) :
  R.v301 (state s) (inputs i) = Zmod.unsigned (N.v301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v301 s i)) at 1.
  unfold R.v301, N.v301.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_302 (s : N.State) (i : N.Inputs) :
  R.v302 (state s) (inputs i) = Zmod.unsigned (N.v302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v302 s i)) at 1.
  unfold R.v302, N.v302.
  rewrite ?node_301.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r82_nr_5F82.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r82_nr_5F82 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_303 (s : N.State) (i : N.Inputs) :
  R.v303 (state s) (inputs i) = Zmod.unsigned (N.v303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v303 s i)) at 1.
  unfold R.v303, N.v303.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_304 (s : N.State) (i : N.Inputs) :
  R.v304 (state s) (inputs i) = Zmod.unsigned (N.v304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v304 s i)) at 1.
  unfold R.v304, N.v304.
  rewrite ?node_303.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r83_nr_5F83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r83_nr_5F83 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_305 (s : N.State) (i : N.Inputs) :
  R.v305 (state s) (inputs i) = Zmod.unsigned (N.v305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v305 s i)) at 1.
  unfold R.v305, N.v305.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_306 (s : N.State) (i : N.Inputs) :
  R.v306 (state s) (inputs i) = Zmod.unsigned (N.v306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v306 s i)) at 1.
  unfold R.v306, N.v306.
  rewrite ?node_305.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r84_nr_5F84.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r84_nr_5F84 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_307 (s : N.State) (i : N.Inputs) :
  R.v307 (state s) (inputs i) = Zmod.unsigned (N.v307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v307 s i)) at 1.
  unfold R.v307, N.v307.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_308 (s : N.State) (i : N.Inputs) :
  R.v308 (state s) (inputs i) = Zmod.unsigned (N.v308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v308 s i)) at 1.
  unfold R.v308, N.v308.
  rewrite ?node_307.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r85_nr_5F85.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r85_nr_5F85 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_309 (s : N.State) (i : N.Inputs) :
  R.v309 (state s) (inputs i) = Zmod.unsigned (N.v309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v309 s i)) at 1.
  unfold R.v309, N.v309.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_310 (s : N.State) (i : N.Inputs) :
  R.v310 (state s) (inputs i) = Zmod.unsigned (N.v310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v310 s i)) at 1.
  unfold R.v310, N.v310.
  rewrite ?node_309.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r86_nr_5F86.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r86_nr_5F86 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_311 (s : N.State) (i : N.Inputs) :
  R.v311 (state s) (inputs i) = Zmod.unsigned (N.v311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v311 s i)) at 1.
  unfold R.v311, N.v311.
  rewrite ?node_292.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_312 (s : N.State) (i : N.Inputs) :
  R.v312 (state s) (inputs i) = Zmod.unsigned (N.v312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v312 s i)) at 1.
  unfold R.v312, N.v312.
  rewrite ?node_311.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r87_nr_5F87.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r87_nr_5F87 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_313 (s : N.State) (i : N.Inputs) :
  R.v313 (state s) (inputs i) = Zmod.unsigned (N.v313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v313 s i)) at 1.
  unfold R.v313, N.v313.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_314 (s : N.State) (i : N.Inputs) :
  R.v314 (state s) (inputs i) = Zmod.unsigned (N.v314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v314 s i)) at 1.
  unfold R.v314, N.v314.
  rewrite ?node_313.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r88_nr_5F88.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r88_nr_5F88 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_315 (s : N.State) (i : N.Inputs) :
  R.v315 (state s) (inputs i) = Zmod.unsigned (N.v315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v315 s i)) at 1.
  unfold R.v315, N.v315.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_316 (s : N.State) (i : N.Inputs) :
  R.v316 (state s) (inputs i) = Zmod.unsigned (N.v316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v316 s i)) at 1.
  unfold R.v316, N.v316.
  rewrite ?node_315.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r89_nr_5F89.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r89_nr_5F89 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_317 (s : N.State) (i : N.Inputs) :
  R.v317 (state s) (inputs i) = Zmod.unsigned (N.v317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v317 s i)) at 1.
  unfold R.v317, N.v317.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_318 (s : N.State) (i : N.Inputs) :
  R.v318 (state s) (inputs i) = Zmod.unsigned (N.v318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v318 s i)) at 1.
  unfold R.v318, N.v318.
  rewrite ?node_317.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r90_nr_5F90.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r90_nr_5F90 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_319 (s : N.State) (i : N.Inputs) :
  R.v319 (state s) (inputs i) = Zmod.unsigned (N.v319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v319 s i)) at 1.
  unfold R.v319, N.v319.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_320 (s : N.State) (i : N.Inputs) :
  R.v320 (state s) (inputs i) = Zmod.unsigned (N.v320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v320 s i)) at 1.
  unfold R.v320, N.v320.
  rewrite ?node_319.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r91_nr_5F91.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r91_nr_5F91 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_321 (s : N.State) (i : N.Inputs) :
  R.v321 (state s) (inputs i) = Zmod.unsigned (N.v321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v321 s i)) at 1.
  unfold R.v321, N.v321.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_322 (s : N.State) (i : N.Inputs) :
  R.v322 (state s) (inputs i) = Zmod.unsigned (N.v322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v322 s i)) at 1.
  unfold R.v322, N.v322.
  rewrite ?node_321.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r92_nr_5F92.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r92_nr_5F92 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_323 (s : N.State) (i : N.Inputs) :
  R.v323 (state s) (inputs i) = Zmod.unsigned (N.v323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v323 s i)) at 1.
  unfold R.v323, N.v323.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_324 (s : N.State) (i : N.Inputs) :
  R.v324 (state s) (inputs i) = Zmod.unsigned (N.v324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v324 s i)) at 1.
  unfold R.v324, N.v324.
  rewrite ?node_323.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r93_nr_5F93.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r93_nr_5F93 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_325 (s : N.State) (i : N.Inputs) :
  R.v325 (state s) (inputs i) = Zmod.unsigned (N.v325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v325 s i)) at 1.
  unfold R.v325, N.v325.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_326 (s : N.State) (i : N.Inputs) :
  R.v326 (state s) (inputs i) = Zmod.unsigned (N.v326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v326 s i)) at 1.
  unfold R.v326, N.v326.
  rewrite ?node_325.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r94_nr_5F94.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r94_nr_5F94 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_327 (s : N.State) (i : N.Inputs) :
  R.v327 (state s) (inputs i) = Zmod.unsigned (N.v327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v327 s i)) at 1.
  unfold R.v327, N.v327.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_328 (s : N.State) (i : N.Inputs) :
  R.v328 (state s) (inputs i) = Zmod.unsigned (N.v328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v328 s i)) at 1.
  unfold R.v328, N.v328.
  rewrite ?node_327.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r95_nr_5F95.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r95_nr_5F95 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_329 (s : N.State) (i : N.Inputs) :
  R.v329 (state s) (inputs i) = Zmod.unsigned (N.v329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v329 s i)) at 1.
  unfold R.v329, N.v329.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_330 (s : N.State) (i : N.Inputs) :
  R.v330 (state s) (inputs i) = Zmod.unsigned (N.v330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v330 s i)) at 1.
  unfold R.v330, N.v330.
  unfold R.v33, N.v33.
  rewrite ?node_329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_331 (s : N.State) (i : N.Inputs) :
  R.v331 (state s) (inputs i) = Zmod.unsigned (N.v331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v331 s i)) at 1.
  unfold R.v331, N.v331.
  unfold R.v35, N.v35.
  rewrite ?node_329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_332 (s : N.State) (i : N.Inputs) :
  R.v332 (state s) (inputs i) = Zmod.unsigned (N.v332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v332 s i)) at 1.
  unfold R.v332, N.v332.
  rewrite ?node_330.
  rewrite ?node_331.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_333 (s : N.State) (i : N.Inputs) :
  R.v333 (state s) (inputs i) = Zmod.unsigned (N.v333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v333 s i)) at 1.
  unfold R.v333, N.v333.
  unfold R.v39, N.v39.
  rewrite ?node_329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_334 (s : N.State) (i : N.Inputs) :
  R.v334 (state s) (inputs i) = Zmod.unsigned (N.v334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v334 s i)) at 1.
  unfold R.v334, N.v334.
  unfold R.v42, N.v42.
  rewrite ?node_329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_335 (s : N.State) (i : N.Inputs) :
  R.v335 (state s) (inputs i) = Zmod.unsigned (N.v335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v335 s i)) at 1.
  unfold R.v335, N.v335.
  unfold R.v45, N.v45.
  rewrite ?node_329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_336 (s : N.State) (i : N.Inputs) :
  R.v336 (state s) (inputs i) = Zmod.unsigned (N.v336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v336 s i)) at 1.
  unfold R.v336, N.v336.
  unfold R.v47, N.v47.
  rewrite ?node_329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_337 (s : N.State) (i : N.Inputs) :
  R.v337 (state s) (inputs i) = Zmod.unsigned (N.v337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v337 s i)) at 1.
  unfold R.v337, N.v337.
  rewrite ?node_335.
  rewrite ?node_336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_338 (s : N.State) (i : N.Inputs) :
  R.v338 (state s) (inputs i) = Zmod.unsigned (N.v338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v338 s i)) at 1.
  unfold R.v338, N.v338.
  unfold R.v11, N.v11.
  rewrite ?node_50.
  rewrite ?node_337.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_339 (s : N.State) (i : N.Inputs) :
  R.v339 (state s) (inputs i) = Zmod.unsigned (N.v339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v339 s i)) at 1.
  unfold R.v339, N.v339.
  rewrite ?node_44.
  rewrite ?node_334.
  rewrite ?node_338.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_340 (s : N.State) (i : N.Inputs) :
  R.v340 (state s) (inputs i) = Zmod.unsigned (N.v340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v340 s i)) at 1.
  unfold R.v340, N.v340.
  rewrite ?node_41.
  rewrite ?node_333.
  rewrite ?node_339.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_341 (s : N.State) (i : N.Inputs) :
  R.v341 (state s) (inputs i) = Zmod.unsigned (N.v341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v341 s i)) at 1.
  unfold R.v341, N.v341.
  rewrite ?node_38.
  rewrite ?node_332.
  rewrite ?node_340.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_342 (s : N.State) (i : N.Inputs) :
  R.v342 (state s) (inputs i) = Zmod.unsigned (N.v342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v342 s i)) at 1.
  unfold R.v342, N.v342.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_343 (s : N.State) (i : N.Inputs) :
  R.v343 (state s) (inputs i) = Zmod.unsigned (N.v343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v343 s i)) at 1.
  unfold R.v343, N.v343.
  rewrite ?node_342.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r96_nr_5F96.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r96_nr_5F96 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_344 (s : N.State) (i : N.Inputs) :
  R.v344 (state s) (inputs i) = Zmod.unsigned (N.v344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v344 s i)) at 1.
  unfold R.v344, N.v344.
  unfold R.v6, N.v6.
  rewrite ?node_333.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_345 (s : N.State) (i : N.Inputs) :
  R.v345 (state s) (inputs i) = Zmod.unsigned (N.v345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v345 s i)) at 1.
  unfold R.v345, N.v345.
  unfold R.v19, N.v19.
  rewrite ?node_332.
  rewrite ?node_344.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_346 (s : N.State) (i : N.Inputs) :
  R.v346 (state s) (inputs i) = Zmod.unsigned (N.v346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v346 s i)) at 1.
  unfold R.v346, N.v346.
  rewrite ?node_345.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_347 (s : N.State) (i : N.Inputs) :
  R.v347 (state s) (inputs i) = Zmod.unsigned (N.v347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v347 s i)) at 1.
  unfold R.v347, N.v347.
  rewrite ?node_346.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r97_nr_5F97.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r97_nr_5F97 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_348 (s : N.State) (i : N.Inputs) :
  R.v348 (state s) (inputs i) = Zmod.unsigned (N.v348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v348 s i)) at 1.
  unfold R.v348, N.v348.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_349 (s : N.State) (i : N.Inputs) :
  R.v349 (state s) (inputs i) = Zmod.unsigned (N.v349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v349 s i)) at 1.
  unfold R.v349, N.v349.
  rewrite ?node_348.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r98_nr_5F98.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r98_nr_5F98 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_350 (s : N.State) (i : N.Inputs) :
  R.v350 (state s) (inputs i) = Zmod.unsigned (N.v350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v350 s i)) at 1.
  unfold R.v350, N.v350.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_351 (s : N.State) (i : N.Inputs) :
  R.v351 (state s) (inputs i) = Zmod.unsigned (N.v351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v351 s i)) at 1.
  unfold R.v351, N.v351.
  rewrite ?node_350.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r99_nr_5F99.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r99_nr_5F99 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_352 (s : N.State) (i : N.Inputs) :
  R.v352 (state s) (inputs i) = Zmod.unsigned (N.v352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v352 s i)) at 1.
  unfold R.v352, N.v352.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_353 (s : N.State) (i : N.Inputs) :
  R.v353 (state s) (inputs i) = Zmod.unsigned (N.v353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v353 s i)) at 1.
  unfold R.v353, N.v353.
  rewrite ?node_352.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r100_nr_5F100.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r100_nr_5F100 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_354 (s : N.State) (i : N.Inputs) :
  R.v354 (state s) (inputs i) = Zmod.unsigned (N.v354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v354 s i)) at 1.
  unfold R.v354, N.v354.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_355 (s : N.State) (i : N.Inputs) :
  R.v355 (state s) (inputs i) = Zmod.unsigned (N.v355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v355 s i)) at 1.
  unfold R.v355, N.v355.
  rewrite ?node_354.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r101_nr_5F101.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r101_nr_5F101 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_356 (s : N.State) (i : N.Inputs) :
  R.v356 (state s) (inputs i) = Zmod.unsigned (N.v356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v356 s i)) at 1.
  unfold R.v356, N.v356.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_357 (s : N.State) (i : N.Inputs) :
  R.v357 (state s) (inputs i) = Zmod.unsigned (N.v357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v357 s i)) at 1.
  unfold R.v357, N.v357.
  rewrite ?node_356.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r102_nr_5F102.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r102_nr_5F102 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_358 (s : N.State) (i : N.Inputs) :
  R.v358 (state s) (inputs i) = Zmod.unsigned (N.v358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v358 s i)) at 1.
  unfold R.v358, N.v358.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_359 (s : N.State) (i : N.Inputs) :
  R.v359 (state s) (inputs i) = Zmod.unsigned (N.v359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v359 s i)) at 1.
  unfold R.v359, N.v359.
  rewrite ?node_358.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r103_nr_5F103.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r103_nr_5F103 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_360 (s : N.State) (i : N.Inputs) :
  R.v360 (state s) (inputs i) = Zmod.unsigned (N.v360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v360 s i)) at 1.
  unfold R.v360, N.v360.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_361 (s : N.State) (i : N.Inputs) :
  R.v361 (state s) (inputs i) = Zmod.unsigned (N.v361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v361 s i)) at 1.
  unfold R.v361, N.v361.
  rewrite ?node_360.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r104_nr_5F104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r104_nr_5F104 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_362 (s : N.State) (i : N.Inputs) :
  R.v362 (state s) (inputs i) = Zmod.unsigned (N.v362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v362 s i)) at 1.
  unfold R.v362, N.v362.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_363 (s : N.State) (i : N.Inputs) :
  R.v363 (state s) (inputs i) = Zmod.unsigned (N.v363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v363 s i)) at 1.
  unfold R.v363, N.v363.
  rewrite ?node_362.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r105_nr_5F105.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r105_nr_5F105 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_364 (s : N.State) (i : N.Inputs) :
  R.v364 (state s) (inputs i) = Zmod.unsigned (N.v364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v364 s i)) at 1.
  unfold R.v364, N.v364.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_365 (s : N.State) (i : N.Inputs) :
  R.v365 (state s) (inputs i) = Zmod.unsigned (N.v365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v365 s i)) at 1.
  unfold R.v365, N.v365.
  rewrite ?node_364.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r106_nr_5F106.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r106_nr_5F106 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_366 (s : N.State) (i : N.Inputs) :
  R.v366 (state s) (inputs i) = Zmod.unsigned (N.v366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v366 s i)) at 1.
  unfold R.v366, N.v366.
  rewrite ?node_345.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_367 (s : N.State) (i : N.Inputs) :
  R.v367 (state s) (inputs i) = Zmod.unsigned (N.v367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v367 s i)) at 1.
  unfold R.v367, N.v367.
  rewrite ?node_366.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r107_nr_5F107.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r107_nr_5F107 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_368 (s : N.State) (i : N.Inputs) :
  R.v368 (state s) (inputs i) = Zmod.unsigned (N.v368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v368 s i)) at 1.
  unfold R.v368, N.v368.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_369 (s : N.State) (i : N.Inputs) :
  R.v369 (state s) (inputs i) = Zmod.unsigned (N.v369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v369 s i)) at 1.
  unfold R.v369, N.v369.
  rewrite ?node_368.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r108_nr_5F108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r108_nr_5F108 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_370 (s : N.State) (i : N.Inputs) :
  R.v370 (state s) (inputs i) = Zmod.unsigned (N.v370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v370 s i)) at 1.
  unfold R.v370, N.v370.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_371 (s : N.State) (i : N.Inputs) :
  R.v371 (state s) (inputs i) = Zmod.unsigned (N.v371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v371 s i)) at 1.
  unfold R.v371, N.v371.
  rewrite ?node_370.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r109_nr_5F109.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r109_nr_5F109 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_372 (s : N.State) (i : N.Inputs) :
  R.v372 (state s) (inputs i) = Zmod.unsigned (N.v372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v372 s i)) at 1.
  unfold R.v372, N.v372.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_373 (s : N.State) (i : N.Inputs) :
  R.v373 (state s) (inputs i) = Zmod.unsigned (N.v373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v373 s i)) at 1.
  unfold R.v373, N.v373.
  rewrite ?node_372.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r110_nr_5F110.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r110_nr_5F110 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_374 (s : N.State) (i : N.Inputs) :
  R.v374 (state s) (inputs i) = Zmod.unsigned (N.v374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v374 s i)) at 1.
  unfold R.v374, N.v374.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_375 (s : N.State) (i : N.Inputs) :
  R.v375 (state s) (inputs i) = Zmod.unsigned (N.v375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v375 s i)) at 1.
  unfold R.v375, N.v375.
  rewrite ?node_374.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r111_nr_5F111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r111_nr_5F111 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_376 (s : N.State) (i : N.Inputs) :
  R.v376 (state s) (inputs i) = Zmod.unsigned (N.v376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v376 s i)) at 1.
  unfold R.v376, N.v376.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_377 (s : N.State) (i : N.Inputs) :
  R.v377 (state s) (inputs i) = Zmod.unsigned (N.v377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v377 s i)) at 1.
  unfold R.v377, N.v377.
  rewrite ?node_376.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r112_nr_5F112.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r112_nr_5F112 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_378 (s : N.State) (i : N.Inputs) :
  R.v378 (state s) (inputs i) = Zmod.unsigned (N.v378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v378 s i)) at 1.
  unfold R.v378, N.v378.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_379 (s : N.State) (i : N.Inputs) :
  R.v379 (state s) (inputs i) = Zmod.unsigned (N.v379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v379 s i)) at 1.
  unfold R.v379, N.v379.
  rewrite ?node_378.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r113_nr_5F113.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r113_nr_5F113 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_380 (s : N.State) (i : N.Inputs) :
  R.v380 (state s) (inputs i) = Zmod.unsigned (N.v380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v380 s i)) at 1.
  unfold R.v380, N.v380.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_381 (s : N.State) (i : N.Inputs) :
  R.v381 (state s) (inputs i) = Zmod.unsigned (N.v381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v381 s i)) at 1.
  unfold R.v381, N.v381.
  rewrite ?node_380.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r114_nr_5F114.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r114_nr_5F114 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_382 (s : N.State) (i : N.Inputs) :
  R.v382 (state s) (inputs i) = Zmod.unsigned (N.v382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v382 s i)) at 1.
  unfold R.v382, N.v382.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_383 (s : N.State) (i : N.Inputs) :
  R.v383 (state s) (inputs i) = Zmod.unsigned (N.v383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v383 s i)) at 1.
  unfold R.v383, N.v383.
  rewrite ?node_382.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r115_nr_5F115.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r115_nr_5F115 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_384 (s : N.State) (i : N.Inputs) :
  R.v384 (state s) (inputs i) = Zmod.unsigned (N.v384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v384 s i)) at 1.
  unfold R.v384, N.v384.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_385 (s : N.State) (i : N.Inputs) :
  R.v385 (state s) (inputs i) = Zmod.unsigned (N.v385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v385 s i)) at 1.
  unfold R.v385, N.v385.
  rewrite ?node_384.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r116_nr_5F116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r116_nr_5F116 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_386 (s : N.State) (i : N.Inputs) :
  R.v386 (state s) (inputs i) = Zmod.unsigned (N.v386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v386 s i)) at 1.
  unfold R.v386, N.v386.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_387 (s : N.State) (i : N.Inputs) :
  R.v387 (state s) (inputs i) = Zmod.unsigned (N.v387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v387 s i)) at 1.
  unfold R.v387, N.v387.
  unfold R.v33, N.v33.
  rewrite ?node_386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_388 (s : N.State) (i : N.Inputs) :
  R.v388 (state s) (inputs i) = Zmod.unsigned (N.v388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v388 s i)) at 1.
  unfold R.v388, N.v388.
  unfold R.v35, N.v35.
  rewrite ?node_386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_389 (s : N.State) (i : N.Inputs) :
  R.v389 (state s) (inputs i) = Zmod.unsigned (N.v389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v389 s i)) at 1.
  unfold R.v389, N.v389.
  rewrite ?node_387.
  rewrite ?node_388.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_390 (s : N.State) (i : N.Inputs) :
  R.v390 (state s) (inputs i) = Zmod.unsigned (N.v390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v390 s i)) at 1.
  unfold R.v390, N.v390.
  unfold R.v39, N.v39.
  rewrite ?node_386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_391 (s : N.State) (i : N.Inputs) :
  R.v391 (state s) (inputs i) = Zmod.unsigned (N.v391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v391 s i)) at 1.
  unfold R.v391, N.v391.
  unfold R.v42, N.v42.
  rewrite ?node_386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_392 (s : N.State) (i : N.Inputs) :
  R.v392 (state s) (inputs i) = Zmod.unsigned (N.v392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v392 s i)) at 1.
  unfold R.v392, N.v392.
  unfold R.v45, N.v45.
  rewrite ?node_386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_393 (s : N.State) (i : N.Inputs) :
  R.v393 (state s) (inputs i) = Zmod.unsigned (N.v393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v393 s i)) at 1.
  unfold R.v393, N.v393.
  unfold R.v47, N.v47.
  rewrite ?node_386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_394 (s : N.State) (i : N.Inputs) :
  R.v394 (state s) (inputs i) = Zmod.unsigned (N.v394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v394 s i)) at 1.
  unfold R.v394, N.v394.
  rewrite ?node_392.
  rewrite ?node_393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_395 (s : N.State) (i : N.Inputs) :
  R.v395 (state s) (inputs i) = Zmod.unsigned (N.v395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v395 s i)) at 1.
  unfold R.v395, N.v395.
  unfold R.v11, N.v11.
  rewrite ?node_50.
  rewrite ?node_394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_396 (s : N.State) (i : N.Inputs) :
  R.v396 (state s) (inputs i) = Zmod.unsigned (N.v396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v396 s i)) at 1.
  unfold R.v396, N.v396.
  rewrite ?node_44.
  rewrite ?node_391.
  rewrite ?node_395.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_397 (s : N.State) (i : N.Inputs) :
  R.v397 (state s) (inputs i) = Zmod.unsigned (N.v397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v397 s i)) at 1.
  unfold R.v397, N.v397.
  rewrite ?node_41.
  rewrite ?node_390.
  rewrite ?node_396.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_398 (s : N.State) (i : N.Inputs) :
  R.v398 (state s) (inputs i) = Zmod.unsigned (N.v398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v398 s i)) at 1.
  unfold R.v398, N.v398.
  rewrite ?node_38.
  rewrite ?node_389.
  rewrite ?node_397.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_399 (s : N.State) (i : N.Inputs) :
  R.v399 (state s) (inputs i) = Zmod.unsigned (N.v399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v399 s i)) at 1.
  unfold R.v399, N.v399.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_400 (s : N.State) (i : N.Inputs) :
  R.v400 (state s) (inputs i) = Zmod.unsigned (N.v400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v400 s i)) at 1.
  unfold R.v400, N.v400.
  rewrite ?node_399.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r117_nr_5F117.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r117_nr_5F117 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_401 (s : N.State) (i : N.Inputs) :
  R.v401 (state s) (inputs i) = Zmod.unsigned (N.v401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v401 s i)) at 1.
  unfold R.v401, N.v401.
  unfold R.v6, N.v6.
  rewrite ?node_390.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_402 (s : N.State) (i : N.Inputs) :
  R.v402 (state s) (inputs i) = Zmod.unsigned (N.v402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v402 s i)) at 1.
  unfold R.v402, N.v402.
  unfold R.v19, N.v19.
  rewrite ?node_389.
  rewrite ?node_401.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_403 (s : N.State) (i : N.Inputs) :
  R.v403 (state s) (inputs i) = Zmod.unsigned (N.v403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v403 s i)) at 1.
  unfold R.v403, N.v403.
  rewrite ?node_402.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_404 (s : N.State) (i : N.Inputs) :
  R.v404 (state s) (inputs i) = Zmod.unsigned (N.v404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v404 s i)) at 1.
  unfold R.v404, N.v404.
  rewrite ?node_403.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r118_nr_5F118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r118_nr_5F118 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_405 (s : N.State) (i : N.Inputs) :
  R.v405 (state s) (inputs i) = Zmod.unsigned (N.v405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v405 s i)) at 1.
  unfold R.v405, N.v405.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_406 (s : N.State) (i : N.Inputs) :
  R.v406 (state s) (inputs i) = Zmod.unsigned (N.v406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v406 s i)) at 1.
  unfold R.v406, N.v406.
  rewrite ?node_405.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r119_nr_5F119.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r119_nr_5F119 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_407 (s : N.State) (i : N.Inputs) :
  R.v407 (state s) (inputs i) = Zmod.unsigned (N.v407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v407 s i)) at 1.
  unfold R.v407, N.v407.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_408 (s : N.State) (i : N.Inputs) :
  R.v408 (state s) (inputs i) = Zmod.unsigned (N.v408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v408 s i)) at 1.
  unfold R.v408, N.v408.
  rewrite ?node_407.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r120_nr_5F120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r120_nr_5F120 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_409 (s : N.State) (i : N.Inputs) :
  R.v409 (state s) (inputs i) = Zmod.unsigned (N.v409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v409 s i)) at 1.
  unfold R.v409, N.v409.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_410 (s : N.State) (i : N.Inputs) :
  R.v410 (state s) (inputs i) = Zmod.unsigned (N.v410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v410 s i)) at 1.
  unfold R.v410, N.v410.
  rewrite ?node_409.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r121_nr_5F121.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r121_nr_5F121 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_411 (s : N.State) (i : N.Inputs) :
  R.v411 (state s) (inputs i) = Zmod.unsigned (N.v411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v411 s i)) at 1.
  unfold R.v411, N.v411.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_412 (s : N.State) (i : N.Inputs) :
  R.v412 (state s) (inputs i) = Zmod.unsigned (N.v412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v412 s i)) at 1.
  unfold R.v412, N.v412.
  rewrite ?node_411.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r122_nr_5F122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r122_nr_5F122 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_413 (s : N.State) (i : N.Inputs) :
  R.v413 (state s) (inputs i) = Zmod.unsigned (N.v413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v413 s i)) at 1.
  unfold R.v413, N.v413.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_414 (s : N.State) (i : N.Inputs) :
  R.v414 (state s) (inputs i) = Zmod.unsigned (N.v414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v414 s i)) at 1.
  unfold R.v414, N.v414.
  rewrite ?node_413.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r123_nr_5F123.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r123_nr_5F123 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_415 (s : N.State) (i : N.Inputs) :
  R.v415 (state s) (inputs i) = Zmod.unsigned (N.v415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v415 s i)) at 1.
  unfold R.v415, N.v415.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_416 (s : N.State) (i : N.Inputs) :
  R.v416 (state s) (inputs i) = Zmod.unsigned (N.v416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v416 s i)) at 1.
  unfold R.v416, N.v416.
  rewrite ?node_415.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r124_nr_5F124.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r124_nr_5F124 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_417 (s : N.State) (i : N.Inputs) :
  R.v417 (state s) (inputs i) = Zmod.unsigned (N.v417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v417 s i)) at 1.
  unfold R.v417, N.v417.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_418 (s : N.State) (i : N.Inputs) :
  R.v418 (state s) (inputs i) = Zmod.unsigned (N.v418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v418 s i)) at 1.
  unfold R.v418, N.v418.
  rewrite ?node_417.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r125_nr_5F125.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r125_nr_5F125 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_419 (s : N.State) (i : N.Inputs) :
  R.v419 (state s) (inputs i) = Zmod.unsigned (N.v419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v419 s i)) at 1.
  unfold R.v419, N.v419.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_420 (s : N.State) (i : N.Inputs) :
  R.v420 (state s) (inputs i) = Zmod.unsigned (N.v420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v420 s i)) at 1.
  unfold R.v420, N.v420.
  rewrite ?node_419.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r126_nr_5F126.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r126_nr_5F126 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_421 (s : N.State) (i : N.Inputs) :
  R.v421 (state s) (inputs i) = Zmod.unsigned (N.v421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v421 s i)) at 1.
  unfold R.v421, N.v421.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_422 (s : N.State) (i : N.Inputs) :
  R.v422 (state s) (inputs i) = Zmod.unsigned (N.v422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v422 s i)) at 1.
  unfold R.v422, N.v422.
  rewrite ?node_421.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r127_nr_5F127.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r127_nr_5F127 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_423 (s : N.State) (i : N.Inputs) :
  R.v423 (state s) (inputs i) = Zmod.unsigned (N.v423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v423 s i)) at 1.
  unfold R.v423, N.v423.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_424 (s : N.State) (i : N.Inputs) :
  R.v424 (state s) (inputs i) = Zmod.unsigned (N.v424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v424 s i)) at 1.
  unfold R.v424, N.v424.
  rewrite ?node_423.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r128_nr_5F128.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r128_nr_5F128 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_425 (s : N.State) (i : N.Inputs) :
  R.v425 (state s) (inputs i) = Zmod.unsigned (N.v425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v425 s i)) at 1.
  unfold R.v425, N.v425.
  rewrite ?node_402.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_426 (s : N.State) (i : N.Inputs) :
  R.v426 (state s) (inputs i) = Zmod.unsigned (N.v426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v426 s i)) at 1.
  unfold R.v426, N.v426.
  rewrite ?node_425.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r129_nr_5F129.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r129_nr_5F129 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_427 (s : N.State) (i : N.Inputs) :
  R.v427 (state s) (inputs i) = Zmod.unsigned (N.v427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v427 s i)) at 1.
  unfold R.v427, N.v427.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_428 (s : N.State) (i : N.Inputs) :
  R.v428 (state s) (inputs i) = Zmod.unsigned (N.v428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v428 s i)) at 1.
  unfold R.v428, N.v428.
  rewrite ?node_427.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r130_nr_5F130.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r130_nr_5F130 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_429 (s : N.State) (i : N.Inputs) :
  R.v429 (state s) (inputs i) = Zmod.unsigned (N.v429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v429 s i)) at 1.
  unfold R.v429, N.v429.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_430 (s : N.State) (i : N.Inputs) :
  R.v430 (state s) (inputs i) = Zmod.unsigned (N.v430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v430 s i)) at 1.
  unfold R.v430, N.v430.
  rewrite ?node_429.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r131_nr_5F131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r131_nr_5F131 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_431 (s : N.State) (i : N.Inputs) :
  R.v431 (state s) (inputs i) = Zmod.unsigned (N.v431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v431 s i)) at 1.
  unfold R.v431, N.v431.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_432 (s : N.State) (i : N.Inputs) :
  R.v432 (state s) (inputs i) = Zmod.unsigned (N.v432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v432 s i)) at 1.
  unfold R.v432, N.v432.
  rewrite ?node_431.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r132_nr_5F132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r132_nr_5F132 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_433 (s : N.State) (i : N.Inputs) :
  R.v433 (state s) (inputs i) = Zmod.unsigned (N.v433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v433 s i)) at 1.
  unfold R.v433, N.v433.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_434 (s : N.State) (i : N.Inputs) :
  R.v434 (state s) (inputs i) = Zmod.unsigned (N.v434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v434 s i)) at 1.
  unfold R.v434, N.v434.
  rewrite ?node_433.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r133_nr_5F133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r133_nr_5F133 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_435 (s : N.State) (i : N.Inputs) :
  R.v435 (state s) (inputs i) = Zmod.unsigned (N.v435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v435 s i)) at 1.
  unfold R.v435, N.v435.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_436 (s : N.State) (i : N.Inputs) :
  R.v436 (state s) (inputs i) = Zmod.unsigned (N.v436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v436 s i)) at 1.
  unfold R.v436, N.v436.
  rewrite ?node_435.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r134_nr_5F134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r134_nr_5F134 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_437 (s : N.State) (i : N.Inputs) :
  R.v437 (state s) (inputs i) = Zmod.unsigned (N.v437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v437 s i)) at 1.
  unfold R.v437, N.v437.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_438 (s : N.State) (i : N.Inputs) :
  R.v438 (state s) (inputs i) = Zmod.unsigned (N.v438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v438 s i)) at 1.
  unfold R.v438, N.v438.
  rewrite ?node_437.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r135_nr_5F135.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r135_nr_5F135 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_439 (s : N.State) (i : N.Inputs) :
  R.v439 (state s) (inputs i) = Zmod.unsigned (N.v439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v439 s i)) at 1.
  unfold R.v439, N.v439.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_440 (s : N.State) (i : N.Inputs) :
  R.v440 (state s) (inputs i) = Zmod.unsigned (N.v440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v440 s i)) at 1.
  unfold R.v440, N.v440.
  rewrite ?node_439.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r136_nr_5F136.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r136_nr_5F136 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_441 (s : N.State) (i : N.Inputs) :
  R.v441 (state s) (inputs i) = Zmod.unsigned (N.v441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v441 s i)) at 1.
  unfold R.v441, N.v441.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_442 (s : N.State) (i : N.Inputs) :
  R.v442 (state s) (inputs i) = Zmod.unsigned (N.v442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v442 s i)) at 1.
  unfold R.v442, N.v442.
  rewrite ?node_441.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r137_nr_5F137.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r137_nr_5F137 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_443 (s : N.State) (i : N.Inputs) :
  R.v443 (state s) (inputs i) = Zmod.unsigned (N.v443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v443 s i)) at 1.
  unfold R.v443, N.v443.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_444 (s : N.State) (i : N.Inputs) :
  R.v444 (state s) (inputs i) = Zmod.unsigned (N.v444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v444 s i)) at 1.
  unfold R.v444, N.v444.
  rewrite ?node_443.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r138_nr_5F138.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r138_nr_5F138 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_445 (s : N.State) (i : N.Inputs) :
  R.v445 (state s) (inputs i) = Zmod.unsigned (N.v445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v445 s i)) at 1.
  unfold R.v445, N.v445.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_446 (s : N.State) (i : N.Inputs) :
  R.v446 (state s) (inputs i) = Zmod.unsigned (N.v446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v446 s i)) at 1.
  unfold R.v446, N.v446.
  rewrite ?node_445.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r139_nr_5F139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r139_nr_5F139 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_447 (s : N.State) (i : N.Inputs) :
  R.v447 (state s) (inputs i) = Zmod.unsigned (N.v447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v447 s i)) at 1.
  unfold R.v447, N.v447.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_448 (s : N.State) (i : N.Inputs) :
  R.v448 (state s) (inputs i) = Zmod.unsigned (N.v448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v448 s i)) at 1.
  unfold R.v448, N.v448.
  unfold R.v33, N.v33.
  rewrite ?node_447.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_449 (s : N.State) (i : N.Inputs) :
  R.v449 (state s) (inputs i) = Zmod.unsigned (N.v449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v449 s i)) at 1.
  unfold R.v449, N.v449.
  unfold R.v35, N.v35.
  rewrite ?node_447.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_450 (s : N.State) (i : N.Inputs) :
  R.v450 (state s) (inputs i) = Zmod.unsigned (N.v450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v450 s i)) at 1.
  unfold R.v450, N.v450.
  rewrite ?node_448.
  rewrite ?node_449.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_451 (s : N.State) (i : N.Inputs) :
  R.v451 (state s) (inputs i) = Zmod.unsigned (N.v451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v451 s i)) at 1.
  unfold R.v451, N.v451.
  unfold R.v39, N.v39.
  rewrite ?node_447.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_452 (s : N.State) (i : N.Inputs) :
  R.v452 (state s) (inputs i) = Zmod.unsigned (N.v452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v452 s i)) at 1.
  unfold R.v452, N.v452.
  unfold R.v42, N.v42.
  rewrite ?node_447.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_453 (s : N.State) (i : N.Inputs) :
  R.v453 (state s) (inputs i) = Zmod.unsigned (N.v453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v453 s i)) at 1.
  unfold R.v453, N.v453.
  unfold R.v45, N.v45.
  rewrite ?node_447.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_454 (s : N.State) (i : N.Inputs) :
  R.v454 (state s) (inputs i) = Zmod.unsigned (N.v454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v454 s i)) at 1.
  unfold R.v454, N.v454.
  unfold R.v47, N.v47.
  rewrite ?node_447.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_455 (s : N.State) (i : N.Inputs) :
  R.v455 (state s) (inputs i) = Zmod.unsigned (N.v455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v455 s i)) at 1.
  unfold R.v455, N.v455.
  rewrite ?node_453.
  rewrite ?node_454.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_456 (s : N.State) (i : N.Inputs) :
  R.v456 (state s) (inputs i) = Zmod.unsigned (N.v456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v456 s i)) at 1.
  unfold R.v456, N.v456.
  unfold R.v11, N.v11.
  rewrite ?node_50.
  rewrite ?node_455.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_457 (s : N.State) (i : N.Inputs) :
  R.v457 (state s) (inputs i) = Zmod.unsigned (N.v457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v457 s i)) at 1.
  unfold R.v457, N.v457.
  rewrite ?node_44.
  rewrite ?node_452.
  rewrite ?node_456.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_458 (s : N.State) (i : N.Inputs) :
  R.v458 (state s) (inputs i) = Zmod.unsigned (N.v458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v458 s i)) at 1.
  unfold R.v458, N.v458.
  rewrite ?node_41.
  rewrite ?node_451.
  rewrite ?node_457.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_459 (s : N.State) (i : N.Inputs) :
  R.v459 (state s) (inputs i) = Zmod.unsigned (N.v459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v459 s i)) at 1.
  unfold R.v459, N.v459.
  rewrite ?node_38.
  rewrite ?node_450.
  rewrite ?node_458.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_460 (s : N.State) (i : N.Inputs) :
  R.v460 (state s) (inputs i) = Zmod.unsigned (N.v460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v460 s i)) at 1.
  unfold R.v460, N.v460.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_461 (s : N.State) (i : N.Inputs) :
  R.v461 (state s) (inputs i) = Zmod.unsigned (N.v461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v461 s i)) at 1.
  unfold R.v461, N.v461.
  rewrite ?node_460.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r140_nr_5F140.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r140_nr_5F140 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_462 (s : N.State) (i : N.Inputs) :
  R.v462 (state s) (inputs i) = Zmod.unsigned (N.v462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v462 s i)) at 1.
  unfold R.v462, N.v462.
  unfold R.v6, N.v6.
  rewrite ?node_451.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_463 (s : N.State) (i : N.Inputs) :
  R.v463 (state s) (inputs i) = Zmod.unsigned (N.v463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v463 s i)) at 1.
  unfold R.v463, N.v463.
  unfold R.v19, N.v19.
  rewrite ?node_450.
  rewrite ?node_462.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_464 (s : N.State) (i : N.Inputs) :
  R.v464 (state s) (inputs i) = Zmod.unsigned (N.v464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v464 s i)) at 1.
  unfold R.v464, N.v464.
  rewrite ?node_463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_465 (s : N.State) (i : N.Inputs) :
  R.v465 (state s) (inputs i) = Zmod.unsigned (N.v465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v465 s i)) at 1.
  unfold R.v465, N.v465.
  rewrite ?node_464.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r141_nr_5F141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r141_nr_5F141 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_466 (s : N.State) (i : N.Inputs) :
  R.v466 (state s) (inputs i) = Zmod.unsigned (N.v466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v466 s i)) at 1.
  unfold R.v466, N.v466.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_467 (s : N.State) (i : N.Inputs) :
  R.v467 (state s) (inputs i) = Zmod.unsigned (N.v467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v467 s i)) at 1.
  unfold R.v467, N.v467.
  rewrite ?node_466.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r142_nr_5F142.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r142_nr_5F142 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_468 (s : N.State) (i : N.Inputs) :
  R.v468 (state s) (inputs i) = Zmod.unsigned (N.v468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v468 s i)) at 1.
  unfold R.v468, N.v468.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_469 (s : N.State) (i : N.Inputs) :
  R.v469 (state s) (inputs i) = Zmod.unsigned (N.v469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v469 s i)) at 1.
  unfold R.v469, N.v469.
  rewrite ?node_468.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r143_nr_5F143.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r143_nr_5F143 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_470 (s : N.State) (i : N.Inputs) :
  R.v470 (state s) (inputs i) = Zmod.unsigned (N.v470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v470 s i)) at 1.
  unfold R.v470, N.v470.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_471 (s : N.State) (i : N.Inputs) :
  R.v471 (state s) (inputs i) = Zmod.unsigned (N.v471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v471 s i)) at 1.
  unfold R.v471, N.v471.
  rewrite ?node_470.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r144_nr_5F144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r144_nr_5F144 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_472 (s : N.State) (i : N.Inputs) :
  R.v472 (state s) (inputs i) = Zmod.unsigned (N.v472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v472 s i)) at 1.
  unfold R.v472, N.v472.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_473 (s : N.State) (i : N.Inputs) :
  R.v473 (state s) (inputs i) = Zmod.unsigned (N.v473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v473 s i)) at 1.
  unfold R.v473, N.v473.
  rewrite ?node_472.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r145_nr_5F145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r145_nr_5F145 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_474 (s : N.State) (i : N.Inputs) :
  R.v474 (state s) (inputs i) = Zmod.unsigned (N.v474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v474 s i)) at 1.
  unfold R.v474, N.v474.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_475 (s : N.State) (i : N.Inputs) :
  R.v475 (state s) (inputs i) = Zmod.unsigned (N.v475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v475 s i)) at 1.
  unfold R.v475, N.v475.
  rewrite ?node_474.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r146_nr_5F146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r146_nr_5F146 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_476 (s : N.State) (i : N.Inputs) :
  R.v476 (state s) (inputs i) = Zmod.unsigned (N.v476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v476 s i)) at 1.
  unfold R.v476, N.v476.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_477 (s : N.State) (i : N.Inputs) :
  R.v477 (state s) (inputs i) = Zmod.unsigned (N.v477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v477 s i)) at 1.
  unfold R.v477, N.v477.
  rewrite ?node_476.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r147_nr_5F147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r147_nr_5F147 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_478 (s : N.State) (i : N.Inputs) :
  R.v478 (state s) (inputs i) = Zmod.unsigned (N.v478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v478 s i)) at 1.
  unfold R.v478, N.v478.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_479 (s : N.State) (i : N.Inputs) :
  R.v479 (state s) (inputs i) = Zmod.unsigned (N.v479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v479 s i)) at 1.
  unfold R.v479, N.v479.
  rewrite ?node_478.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r148_nr_5F148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r148_nr_5F148 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_480 (s : N.State) (i : N.Inputs) :
  R.v480 (state s) (inputs i) = Zmod.unsigned (N.v480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v480 s i)) at 1.
  unfold R.v480, N.v480.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_481 (s : N.State) (i : N.Inputs) :
  R.v481 (state s) (inputs i) = Zmod.unsigned (N.v481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v481 s i)) at 1.
  unfold R.v481, N.v481.
  rewrite ?node_480.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r149_nr_5F149.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r149_nr_5F149 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_482 (s : N.State) (i : N.Inputs) :
  R.v482 (state s) (inputs i) = Zmod.unsigned (N.v482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v482 s i)) at 1.
  unfold R.v482, N.v482.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_483 (s : N.State) (i : N.Inputs) :
  R.v483 (state s) (inputs i) = Zmod.unsigned (N.v483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v483 s i)) at 1.
  unfold R.v483, N.v483.
  rewrite ?node_482.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r150_nr_5F150.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r150_nr_5F150 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_484 (s : N.State) (i : N.Inputs) :
  R.v484 (state s) (inputs i) = Zmod.unsigned (N.v484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v484 s i)) at 1.
  unfold R.v484, N.v484.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_485 (s : N.State) (i : N.Inputs) :
  R.v485 (state s) (inputs i) = Zmod.unsigned (N.v485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v485 s i)) at 1.
  unfold R.v485, N.v485.
  rewrite ?node_484.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r151_nr_5F151.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r151_nr_5F151 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_486 (s : N.State) (i : N.Inputs) :
  R.v486 (state s) (inputs i) = Zmod.unsigned (N.v486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v486 s i)) at 1.
  unfold R.v486, N.v486.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_487 (s : N.State) (i : N.Inputs) :
  R.v487 (state s) (inputs i) = Zmod.unsigned (N.v487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v487 s i)) at 1.
  unfold R.v487, N.v487.
  rewrite ?node_486.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r152_nr_5F152.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r152_nr_5F152 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_488 (s : N.State) (i : N.Inputs) :
  R.v488 (state s) (inputs i) = Zmod.unsigned (N.v488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v488 s i)) at 1.
  unfold R.v488, N.v488.
  rewrite ?node_463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_489 (s : N.State) (i : N.Inputs) :
  R.v489 (state s) (inputs i) = Zmod.unsigned (N.v489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v489 s i)) at 1.
  unfold R.v489, N.v489.
  rewrite ?node_488.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r153_nr_5F153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r153_nr_5F153 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_490 (s : N.State) (i : N.Inputs) :
  R.v490 (state s) (inputs i) = Zmod.unsigned (N.v490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v490 s i)) at 1.
  unfold R.v490, N.v490.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_491 (s : N.State) (i : N.Inputs) :
  R.v491 (state s) (inputs i) = Zmod.unsigned (N.v491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v491 s i)) at 1.
  unfold R.v491, N.v491.
  rewrite ?node_490.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r154_nr_5F154.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r154_nr_5F154 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_492 (s : N.State) (i : N.Inputs) :
  R.v492 (state s) (inputs i) = Zmod.unsigned (N.v492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v492 s i)) at 1.
  unfold R.v492, N.v492.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_493 (s : N.State) (i : N.Inputs) :
  R.v493 (state s) (inputs i) = Zmod.unsigned (N.v493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v493 s i)) at 1.
  unfold R.v493, N.v493.
  rewrite ?node_492.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r155_nr_5F155.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r155_nr_5F155 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_494 (s : N.State) (i : N.Inputs) :
  R.v494 (state s) (inputs i) = Zmod.unsigned (N.v494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v494 s i)) at 1.
  unfold R.v494, N.v494.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_495 (s : N.State) (i : N.Inputs) :
  R.v495 (state s) (inputs i) = Zmod.unsigned (N.v495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v495 s i)) at 1.
  unfold R.v495, N.v495.
  rewrite ?node_494.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r156_nr_5F156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r156_nr_5F156 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_496 (s : N.State) (i : N.Inputs) :
  R.v496 (state s) (inputs i) = Zmod.unsigned (N.v496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v496 s i)) at 1.
  unfold R.v496, N.v496.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_497 (s : N.State) (i : N.Inputs) :
  R.v497 (state s) (inputs i) = Zmod.unsigned (N.v497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v497 s i)) at 1.
  unfold R.v497, N.v497.
  rewrite ?node_496.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r157_nr_5F157.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r157_nr_5F157 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_498 (s : N.State) (i : N.Inputs) :
  R.v498 (state s) (inputs i) = Zmod.unsigned (N.v498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v498 s i)) at 1.
  unfold R.v498, N.v498.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_499 (s : N.State) (i : N.Inputs) :
  R.v499 (state s) (inputs i) = Zmod.unsigned (N.v499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v499 s i)) at 1.
  unfold R.v499, N.v499.
  rewrite ?node_498.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r158_nr_5F158.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r158_nr_5F158 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_500 (s : N.State) (i : N.Inputs) :
  R.v500 (state s) (inputs i) = Zmod.unsigned (N.v500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v500 s i)) at 1.
  unfold R.v500, N.v500.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_501 (s : N.State) (i : N.Inputs) :
  R.v501 (state s) (inputs i) = Zmod.unsigned (N.v501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v501 s i)) at 1.
  unfold R.v501, N.v501.
  rewrite ?node_500.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r159_nr_5F159.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r159_nr_5F159 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_502 (s : N.State) (i : N.Inputs) :
  R.v502 (state s) (inputs i) = Zmod.unsigned (N.v502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v502 s i)) at 1.
  unfold R.v502, N.v502.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_503 (s : N.State) (i : N.Inputs) :
  R.v503 (state s) (inputs i) = Zmod.unsigned (N.v503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v503 s i)) at 1.
  unfold R.v503, N.v503.
  rewrite ?node_502.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r160_nr_5F160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r160_nr_5F160 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_504 (s : N.State) (i : N.Inputs) :
  R.v504 (state s) (inputs i) = Zmod.unsigned (N.v504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v504 s i)) at 1.
  unfold R.v504, N.v504.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_505 (s : N.State) (i : N.Inputs) :
  R.v505 (state s) (inputs i) = Zmod.unsigned (N.v505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v505 s i)) at 1.
  unfold R.v505, N.v505.
  rewrite ?node_504.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r161_nr_5F161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r161_nr_5F161 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_506 (s : N.State) (i : N.Inputs) :
  R.v506 (state s) (inputs i) = Zmod.unsigned (N.v506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v506 s i)) at 1.
  unfold R.v506, N.v506.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_507 (s : N.State) (i : N.Inputs) :
  R.v507 (state s) (inputs i) = Zmod.unsigned (N.v507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v507 s i)) at 1.
  unfold R.v507, N.v507.
  rewrite ?node_506.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r162_nr_5F162.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r162_nr_5F162 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_508 (s : N.State) (i : N.Inputs) :
  R.v508 (state s) (inputs i) = Zmod.unsigned (N.v508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v508 s i)) at 1.
  unfold R.v508, N.v508.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_509 (s : N.State) (i : N.Inputs) :
  R.v509 (state s) (inputs i) = Zmod.unsigned (N.v509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v509 s i)) at 1.
  unfold R.v509, N.v509.
  rewrite ?node_508.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r163_nr_5F163.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r163_nr_5F163 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_510 (s : N.State) (i : N.Inputs) :
  R.v510 (state s) (inputs i) = Zmod.unsigned (N.v510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v510 s i)) at 1.
  unfold R.v510, N.v510.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_511 (s : N.State) (i : N.Inputs) :
  R.v511 (state s) (inputs i) = Zmod.unsigned (N.v511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v511 s i)) at 1.
  unfold R.v511, N.v511.
  rewrite ?node_510.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r164_nr_5F164.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r164_nr_5F164 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_512 (s : N.State) (i : N.Inputs) :
  R.v512 (state s) (inputs i) = Zmod.unsigned (N.v512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v512 s i)) at 1.
  unfold R.v512, N.v512.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_513 (s : N.State) (i : N.Inputs) :
  R.v513 (state s) (inputs i) = Zmod.unsigned (N.v513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v513 s i)) at 1.
  unfold R.v513, N.v513.
  unfold R.v33, N.v33.
  rewrite ?node_512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_514 (s : N.State) (i : N.Inputs) :
  R.v514 (state s) (inputs i) = Zmod.unsigned (N.v514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v514 s i)) at 1.
  unfold R.v514, N.v514.
  unfold R.v35, N.v35.
  rewrite ?node_512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_515 (s : N.State) (i : N.Inputs) :
  R.v515 (state s) (inputs i) = Zmod.unsigned (N.v515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v515 s i)) at 1.
  unfold R.v515, N.v515.
  rewrite ?node_513.
  rewrite ?node_514.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_516 (s : N.State) (i : N.Inputs) :
  R.v516 (state s) (inputs i) = Zmod.unsigned (N.v516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v516 s i)) at 1.
  unfold R.v516, N.v516.
  unfold R.v39, N.v39.
  rewrite ?node_512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_517 (s : N.State) (i : N.Inputs) :
  R.v517 (state s) (inputs i) = Zmod.unsigned (N.v517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v517 s i)) at 1.
  unfold R.v517, N.v517.
  unfold R.v42, N.v42.
  rewrite ?node_512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_518 (s : N.State) (i : N.Inputs) :
  R.v518 (state s) (inputs i) = Zmod.unsigned (N.v518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v518 s i)) at 1.
  unfold R.v518, N.v518.
  unfold R.v45, N.v45.
  rewrite ?node_512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_519 (s : N.State) (i : N.Inputs) :
  R.v519 (state s) (inputs i) = Zmod.unsigned (N.v519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v519 s i)) at 1.
  unfold R.v519, N.v519.
  unfold R.v47, N.v47.
  rewrite ?node_512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_520 (s : N.State) (i : N.Inputs) :
  R.v520 (state s) (inputs i) = Zmod.unsigned (N.v520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v520 s i)) at 1.
  unfold R.v520, N.v520.
  rewrite ?node_518.
  rewrite ?node_519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_521 (s : N.State) (i : N.Inputs) :
  R.v521 (state s) (inputs i) = Zmod.unsigned (N.v521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v521 s i)) at 1.
  unfold R.v521, N.v521.
  unfold R.v11, N.v11.
  rewrite ?node_50.
  rewrite ?node_520.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_522 (s : N.State) (i : N.Inputs) :
  R.v522 (state s) (inputs i) = Zmod.unsigned (N.v522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v522 s i)) at 1.
  unfold R.v522, N.v522.
  rewrite ?node_44.
  rewrite ?node_517.
  rewrite ?node_521.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_523 (s : N.State) (i : N.Inputs) :
  R.v523 (state s) (inputs i) = Zmod.unsigned (N.v523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v523 s i)) at 1.
  unfold R.v523, N.v523.
  rewrite ?node_41.
  rewrite ?node_516.
  rewrite ?node_522.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_524 (s : N.State) (i : N.Inputs) :
  R.v524 (state s) (inputs i) = Zmod.unsigned (N.v524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v524 s i)) at 1.
  unfold R.v524, N.v524.
  rewrite ?node_38.
  rewrite ?node_515.
  rewrite ?node_523.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_525 (s : N.State) (i : N.Inputs) :
  R.v525 (state s) (inputs i) = Zmod.unsigned (N.v525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v525 s i)) at 1.
  unfold R.v525, N.v525.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_526 (s : N.State) (i : N.Inputs) :
  R.v526 (state s) (inputs i) = Zmod.unsigned (N.v526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v526 s i)) at 1.
  unfold R.v526, N.v526.
  rewrite ?node_525.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r165_nr_5F165.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r165_nr_5F165 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_527 (s : N.State) (i : N.Inputs) :
  R.v527 (state s) (inputs i) = Zmod.unsigned (N.v527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v527 s i)) at 1.
  unfold R.v527, N.v527.
  unfold R.v6, N.v6.
  rewrite ?node_516.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_528 (s : N.State) (i : N.Inputs) :
  R.v528 (state s) (inputs i) = Zmod.unsigned (N.v528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v528 s i)) at 1.
  unfold R.v528, N.v528.
  unfold R.v19, N.v19.
  rewrite ?node_515.
  rewrite ?node_527.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_529 (s : N.State) (i : N.Inputs) :
  R.v529 (state s) (inputs i) = Zmod.unsigned (N.v529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v529 s i)) at 1.
  unfold R.v529, N.v529.
  rewrite ?node_528.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_530 (s : N.State) (i : N.Inputs) :
  R.v530 (state s) (inputs i) = Zmod.unsigned (N.v530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v530 s i)) at 1.
  unfold R.v530, N.v530.
  rewrite ?node_529.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r166_nr_5F166.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r166_nr_5F166 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_531 (s : N.State) (i : N.Inputs) :
  R.v531 (state s) (inputs i) = Zmod.unsigned (N.v531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v531 s i)) at 1.
  unfold R.v531, N.v531.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_532 (s : N.State) (i : N.Inputs) :
  R.v532 (state s) (inputs i) = Zmod.unsigned (N.v532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v532 s i)) at 1.
  unfold R.v532, N.v532.
  rewrite ?node_531.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r167_nr_5F167.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r167_nr_5F167 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_533 (s : N.State) (i : N.Inputs) :
  R.v533 (state s) (inputs i) = Zmod.unsigned (N.v533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v533 s i)) at 1.
  unfold R.v533, N.v533.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_534 (s : N.State) (i : N.Inputs) :
  R.v534 (state s) (inputs i) = Zmod.unsigned (N.v534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v534 s i)) at 1.
  unfold R.v534, N.v534.
  rewrite ?node_533.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r168_nr_5F168.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r168_nr_5F168 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_535 (s : N.State) (i : N.Inputs) :
  R.v535 (state s) (inputs i) = Zmod.unsigned (N.v535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v535 s i)) at 1.
  unfold R.v535, N.v535.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_536 (s : N.State) (i : N.Inputs) :
  R.v536 (state s) (inputs i) = Zmod.unsigned (N.v536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v536 s i)) at 1.
  unfold R.v536, N.v536.
  rewrite ?node_535.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r169_nr_5F169.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r169_nr_5F169 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_537 (s : N.State) (i : N.Inputs) :
  R.v537 (state s) (inputs i) = Zmod.unsigned (N.v537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v537 s i)) at 1.
  unfold R.v537, N.v537.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_538 (s : N.State) (i : N.Inputs) :
  R.v538 (state s) (inputs i) = Zmod.unsigned (N.v538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v538 s i)) at 1.
  unfold R.v538, N.v538.
  rewrite ?node_537.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r170_nr_5F170.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r170_nr_5F170 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_539 (s : N.State) (i : N.Inputs) :
  R.v539 (state s) (inputs i) = Zmod.unsigned (N.v539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v539 s i)) at 1.
  unfold R.v539, N.v539.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_540 (s : N.State) (i : N.Inputs) :
  R.v540 (state s) (inputs i) = Zmod.unsigned (N.v540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v540 s i)) at 1.
  unfold R.v540, N.v540.
  rewrite ?node_539.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r171_nr_5F171.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r171_nr_5F171 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_541 (s : N.State) (i : N.Inputs) :
  R.v541 (state s) (inputs i) = Zmod.unsigned (N.v541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v541 s i)) at 1.
  unfold R.v541, N.v541.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_542 (s : N.State) (i : N.Inputs) :
  R.v542 (state s) (inputs i) = Zmod.unsigned (N.v542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v542 s i)) at 1.
  unfold R.v542, N.v542.
  rewrite ?node_541.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r172_nr_5F172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r172_nr_5F172 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_543 (s : N.State) (i : N.Inputs) :
  R.v543 (state s) (inputs i) = Zmod.unsigned (N.v543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v543 s i)) at 1.
  unfold R.v543, N.v543.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_544 (s : N.State) (i : N.Inputs) :
  R.v544 (state s) (inputs i) = Zmod.unsigned (N.v544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v544 s i)) at 1.
  unfold R.v544, N.v544.
  rewrite ?node_543.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r173_nr_5F173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r173_nr_5F173 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_545 (s : N.State) (i : N.Inputs) :
  R.v545 (state s) (inputs i) = Zmod.unsigned (N.v545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v545 s i)) at 1.
  unfold R.v545, N.v545.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_546 (s : N.State) (i : N.Inputs) :
  R.v546 (state s) (inputs i) = Zmod.unsigned (N.v546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v546 s i)) at 1.
  unfold R.v546, N.v546.
  rewrite ?node_545.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r174_nr_5F174.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r174_nr_5F174 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_547 (s : N.State) (i : N.Inputs) :
  R.v547 (state s) (inputs i) = Zmod.unsigned (N.v547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v547 s i)) at 1.
  unfold R.v547, N.v547.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_548 (s : N.State) (i : N.Inputs) :
  R.v548 (state s) (inputs i) = Zmod.unsigned (N.v548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v548 s i)) at 1.
  unfold R.v548, N.v548.
  rewrite ?node_547.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r175_nr_5F175.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r175_nr_5F175 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_549 (s : N.State) (i : N.Inputs) :
  R.v549 (state s) (inputs i) = Zmod.unsigned (N.v549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v549 s i)) at 1.
  unfold R.v549, N.v549.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_550 (s : N.State) (i : N.Inputs) :
  R.v550 (state s) (inputs i) = Zmod.unsigned (N.v550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v550 s i)) at 1.
  unfold R.v550, N.v550.
  rewrite ?node_549.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r176_nr_5F176.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r176_nr_5F176 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_551 (s : N.State) (i : N.Inputs) :
  R.v551 (state s) (inputs i) = Zmod.unsigned (N.v551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v551 s i)) at 1.
  unfold R.v551, N.v551.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_552 (s : N.State) (i : N.Inputs) :
  R.v552 (state s) (inputs i) = Zmod.unsigned (N.v552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v552 s i)) at 1.
  unfold R.v552, N.v552.
  rewrite ?node_551.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r177_nr_5F177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r177_nr_5F177 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_553 (s : N.State) (i : N.Inputs) :
  R.v553 (state s) (inputs i) = Zmod.unsigned (N.v553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v553 s i)) at 1.
  unfold R.v553, N.v553.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_554 (s : N.State) (i : N.Inputs) :
  R.v554 (state s) (inputs i) = Zmod.unsigned (N.v554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v554 s i)) at 1.
  unfold R.v554, N.v554.
  rewrite ?node_553.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r178_nr_5F178.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r178_nr_5F178 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_555 (s : N.State) (i : N.Inputs) :
  R.v555 (state s) (inputs i) = Zmod.unsigned (N.v555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v555 s i)) at 1.
  unfold R.v555, N.v555.
  rewrite ?node_528.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_556 (s : N.State) (i : N.Inputs) :
  R.v556 (state s) (inputs i) = Zmod.unsigned (N.v556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v556 s i)) at 1.
  unfold R.v556, N.v556.
  rewrite ?node_555.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r179_nr_5F179.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r179_nr_5F179 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_557 (s : N.State) (i : N.Inputs) :
  R.v557 (state s) (inputs i) = Zmod.unsigned (N.v557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v557 s i)) at 1.
  unfold R.v557, N.v557.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_558 (s : N.State) (i : N.Inputs) :
  R.v558 (state s) (inputs i) = Zmod.unsigned (N.v558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v558 s i)) at 1.
  unfold R.v558, N.v558.
  rewrite ?node_557.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r180_nr_5F180.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r180_nr_5F180 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_559 (s : N.State) (i : N.Inputs) :
  R.v559 (state s) (inputs i) = Zmod.unsigned (N.v559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v559 s i)) at 1.
  unfold R.v559, N.v559.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_560 (s : N.State) (i : N.Inputs) :
  R.v560 (state s) (inputs i) = Zmod.unsigned (N.v560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v560 s i)) at 1.
  unfold R.v560, N.v560.
  rewrite ?node_559.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r181_nr_5F181.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r181_nr_5F181 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_561 (s : N.State) (i : N.Inputs) :
  R.v561 (state s) (inputs i) = Zmod.unsigned (N.v561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v561 s i)) at 1.
  unfold R.v561, N.v561.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_562 (s : N.State) (i : N.Inputs) :
  R.v562 (state s) (inputs i) = Zmod.unsigned (N.v562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v562 s i)) at 1.
  unfold R.v562, N.v562.
  rewrite ?node_561.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r182_nr_5F182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r182_nr_5F182 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_563 (s : N.State) (i : N.Inputs) :
  R.v563 (state s) (inputs i) = Zmod.unsigned (N.v563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v563 s i)) at 1.
  unfold R.v563, N.v563.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_564 (s : N.State) (i : N.Inputs) :
  R.v564 (state s) (inputs i) = Zmod.unsigned (N.v564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v564 s i)) at 1.
  unfold R.v564, N.v564.
  rewrite ?node_563.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r183_nr_5F183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r183_nr_5F183 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_565 (s : N.State) (i : N.Inputs) :
  R.v565 (state s) (inputs i) = Zmod.unsigned (N.v565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v565 s i)) at 1.
  unfold R.v565, N.v565.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_566 (s : N.State) (i : N.Inputs) :
  R.v566 (state s) (inputs i) = Zmod.unsigned (N.v566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v566 s i)) at 1.
  unfold R.v566, N.v566.
  rewrite ?node_565.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r184_nr_5F184.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r184_nr_5F184 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_567 (s : N.State) (i : N.Inputs) :
  R.v567 (state s) (inputs i) = Zmod.unsigned (N.v567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v567 s i)) at 1.
  unfold R.v567, N.v567.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_568 (s : N.State) (i : N.Inputs) :
  R.v568 (state s) (inputs i) = Zmod.unsigned (N.v568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v568 s i)) at 1.
  unfold R.v568, N.v568.
  rewrite ?node_567.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r185_nr_5F185.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r185_nr_5F185 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_569 (s : N.State) (i : N.Inputs) :
  R.v569 (state s) (inputs i) = Zmod.unsigned (N.v569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v569 s i)) at 1.
  unfold R.v569, N.v569.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_570 (s : N.State) (i : N.Inputs) :
  R.v570 (state s) (inputs i) = Zmod.unsigned (N.v570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v570 s i)) at 1.
  unfold R.v570, N.v570.
  rewrite ?node_569.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r186_nr_5F186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r186_nr_5F186 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_571 (s : N.State) (i : N.Inputs) :
  R.v571 (state s) (inputs i) = Zmod.unsigned (N.v571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v571 s i)) at 1.
  unfold R.v571, N.v571.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_572 (s : N.State) (i : N.Inputs) :
  R.v572 (state s) (inputs i) = Zmod.unsigned (N.v572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v572 s i)) at 1.
  unfold R.v572, N.v572.
  rewrite ?node_571.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r187_nr_5F187.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r187_nr_5F187 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_573 (s : N.State) (i : N.Inputs) :
  R.v573 (state s) (inputs i) = Zmod.unsigned (N.v573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v573 s i)) at 1.
  unfold R.v573, N.v573.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_574 (s : N.State) (i : N.Inputs) :
  R.v574 (state s) (inputs i) = Zmod.unsigned (N.v574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v574 s i)) at 1.
  unfold R.v574, N.v574.
  rewrite ?node_573.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r188_nr_5F188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r188_nr_5F188 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_575 (s : N.State) (i : N.Inputs) :
  R.v575 (state s) (inputs i) = Zmod.unsigned (N.v575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v575 s i)) at 1.
  unfold R.v575, N.v575.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_576 (s : N.State) (i : N.Inputs) :
  R.v576 (state s) (inputs i) = Zmod.unsigned (N.v576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v576 s i)) at 1.
  unfold R.v576, N.v576.
  rewrite ?node_575.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r189_nr_5F189.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r189_nr_5F189 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_577 (s : N.State) (i : N.Inputs) :
  R.v577 (state s) (inputs i) = Zmod.unsigned (N.v577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v577 s i)) at 1.
  unfold R.v577, N.v577.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_578 (s : N.State) (i : N.Inputs) :
  R.v578 (state s) (inputs i) = Zmod.unsigned (N.v578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v578 s i)) at 1.
  unfold R.v578, N.v578.
  rewrite ?node_577.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r190_nr_5F190.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r190_nr_5F190 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_579 (s : N.State) (i : N.Inputs) :
  R.v579 (state s) (inputs i) = Zmod.unsigned (N.v579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v579 s i)) at 1.
  unfold R.v579, N.v579.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_580 (s : N.State) (i : N.Inputs) :
  R.v580 (state s) (inputs i) = Zmod.unsigned (N.v580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v580 s i)) at 1.
  unfold R.v580, N.v580.
  rewrite ?node_579.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r191_nr_5F191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r191_nr_5F191 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_581 (s : N.State) (i : N.Inputs) :
  R.v581 (state s) (inputs i) = Zmod.unsigned (N.v581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v581 s i)) at 1.
  unfold R.v581, N.v581.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_582 (s : N.State) (i : N.Inputs) :
  R.v582 (state s) (inputs i) = Zmod.unsigned (N.v582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v582 s i)) at 1.
  unfold R.v582, N.v582.
  unfold R.v33, N.v33.
  rewrite ?node_581.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_583 (s : N.State) (i : N.Inputs) :
  R.v583 (state s) (inputs i) = Zmod.unsigned (N.v583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v583 s i)) at 1.
  unfold R.v583, N.v583.
  unfold R.v35, N.v35.
  rewrite ?node_581.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_584 (s : N.State) (i : N.Inputs) :
  R.v584 (state s) (inputs i) = Zmod.unsigned (N.v584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v584 s i)) at 1.
  unfold R.v584, N.v584.
  rewrite ?node_582.
  rewrite ?node_583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_585 (s : N.State) (i : N.Inputs) :
  R.v585 (state s) (inputs i) = Zmod.unsigned (N.v585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v585 s i)) at 1.
  unfold R.v585, N.v585.
  unfold R.v39, N.v39.
  rewrite ?node_581.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_586 (s : N.State) (i : N.Inputs) :
  R.v586 (state s) (inputs i) = Zmod.unsigned (N.v586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v586 s i)) at 1.
  unfold R.v586, N.v586.
  unfold R.v42, N.v42.
  rewrite ?node_581.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_587 (s : N.State) (i : N.Inputs) :
  R.v587 (state s) (inputs i) = Zmod.unsigned (N.v587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v587 s i)) at 1.
  unfold R.v587, N.v587.
  unfold R.v45, N.v45.
  rewrite ?node_581.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_588 (s : N.State) (i : N.Inputs) :
  R.v588 (state s) (inputs i) = Zmod.unsigned (N.v588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v588 s i)) at 1.
  unfold R.v588, N.v588.
  unfold R.v47, N.v47.
  rewrite ?node_581.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_589 (s : N.State) (i : N.Inputs) :
  R.v589 (state s) (inputs i) = Zmod.unsigned (N.v589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v589 s i)) at 1.
  unfold R.v589, N.v589.
  rewrite ?node_587.
  rewrite ?node_588.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_590 (s : N.State) (i : N.Inputs) :
  R.v590 (state s) (inputs i) = Zmod.unsigned (N.v590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v590 s i)) at 1.
  unfold R.v590, N.v590.
  unfold R.v11, N.v11.
  rewrite ?node_50.
  rewrite ?node_589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_591 (s : N.State) (i : N.Inputs) :
  R.v591 (state s) (inputs i) = Zmod.unsigned (N.v591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v591 s i)) at 1.
  unfold R.v591, N.v591.
  rewrite ?node_44.
  rewrite ?node_586.
  rewrite ?node_590.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_592 (s : N.State) (i : N.Inputs) :
  R.v592 (state s) (inputs i) = Zmod.unsigned (N.v592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v592 s i)) at 1.
  unfold R.v592, N.v592.
  rewrite ?node_41.
  rewrite ?node_585.
  rewrite ?node_591.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_593 (s : N.State) (i : N.Inputs) :
  R.v593 (state s) (inputs i) = Zmod.unsigned (N.v593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v593 s i)) at 1.
  unfold R.v593, N.v593.
  rewrite ?node_38.
  rewrite ?node_584.
  rewrite ?node_592.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_594 (s : N.State) (i : N.Inputs) :
  R.v594 (state s) (inputs i) = Zmod.unsigned (N.v594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v594 s i)) at 1.
  unfold R.v594, N.v594.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_595 (s : N.State) (i : N.Inputs) :
  R.v595 (state s) (inputs i) = Zmod.unsigned (N.v595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v595 s i)) at 1.
  unfold R.v595, N.v595.
  rewrite ?node_594.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r192_nr_5F192.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r192_nr_5F192 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_596 (s : N.State) (i : N.Inputs) :
  R.v596 (state s) (inputs i) = Zmod.unsigned (N.v596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v596 s i)) at 1.
  unfold R.v596, N.v596.
  unfold R.v6, N.v6.
  rewrite ?node_585.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_597 (s : N.State) (i : N.Inputs) :
  R.v597 (state s) (inputs i) = Zmod.unsigned (N.v597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v597 s i)) at 1.
  unfold R.v597, N.v597.
  unfold R.v19, N.v19.
  rewrite ?node_584.
  rewrite ?node_596.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_598 (s : N.State) (i : N.Inputs) :
  R.v598 (state s) (inputs i) = Zmod.unsigned (N.v598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v598 s i)) at 1.
  unfold R.v598, N.v598.
  rewrite ?node_597.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_599 (s : N.State) (i : N.Inputs) :
  R.v599 (state s) (inputs i) = Zmod.unsigned (N.v599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v599 s i)) at 1.
  unfold R.v599, N.v599.
  rewrite ?node_598.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r193_nr_5F193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r193_nr_5F193 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_600 (s : N.State) (i : N.Inputs) :
  R.v600 (state s) (inputs i) = Zmod.unsigned (N.v600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v600 s i)) at 1.
  unfold R.v600, N.v600.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_601 (s : N.State) (i : N.Inputs) :
  R.v601 (state s) (inputs i) = Zmod.unsigned (N.v601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v601 s i)) at 1.
  unfold R.v601, N.v601.
  rewrite ?node_600.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r194_nr_5F194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r194_nr_5F194 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_602 (s : N.State) (i : N.Inputs) :
  R.v602 (state s) (inputs i) = Zmod.unsigned (N.v602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v602 s i)) at 1.
  unfold R.v602, N.v602.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_603 (s : N.State) (i : N.Inputs) :
  R.v603 (state s) (inputs i) = Zmod.unsigned (N.v603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v603 s i)) at 1.
  unfold R.v603, N.v603.
  rewrite ?node_602.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r195_nr_5F195.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r195_nr_5F195 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_604 (s : N.State) (i : N.Inputs) :
  R.v604 (state s) (inputs i) = Zmod.unsigned (N.v604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v604 s i)) at 1.
  unfold R.v604, N.v604.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_605 (s : N.State) (i : N.Inputs) :
  R.v605 (state s) (inputs i) = Zmod.unsigned (N.v605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v605 s i)) at 1.
  unfold R.v605, N.v605.
  rewrite ?node_604.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r196_nr_5F196.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r196_nr_5F196 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_606 (s : N.State) (i : N.Inputs) :
  R.v606 (state s) (inputs i) = Zmod.unsigned (N.v606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v606 s i)) at 1.
  unfold R.v606, N.v606.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_607 (s : N.State) (i : N.Inputs) :
  R.v607 (state s) (inputs i) = Zmod.unsigned (N.v607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v607 s i)) at 1.
  unfold R.v607, N.v607.
  rewrite ?node_606.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r197_nr_5F197.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r197_nr_5F197 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_608 (s : N.State) (i : N.Inputs) :
  R.v608 (state s) (inputs i) = Zmod.unsigned (N.v608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v608 s i)) at 1.
  unfold R.v608, N.v608.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_609 (s : N.State) (i : N.Inputs) :
  R.v609 (state s) (inputs i) = Zmod.unsigned (N.v609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v609 s i)) at 1.
  unfold R.v609, N.v609.
  rewrite ?node_608.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r198_nr_5F198.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r198_nr_5F198 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_610 (s : N.State) (i : N.Inputs) :
  R.v610 (state s) (inputs i) = Zmod.unsigned (N.v610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v610 s i)) at 1.
  unfold R.v610, N.v610.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_611 (s : N.State) (i : N.Inputs) :
  R.v611 (state s) (inputs i) = Zmod.unsigned (N.v611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v611 s i)) at 1.
  unfold R.v611, N.v611.
  rewrite ?node_610.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r199_nr_5F199.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r199_nr_5F199 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_612 (s : N.State) (i : N.Inputs) :
  R.v612 (state s) (inputs i) = Zmod.unsigned (N.v612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v612 s i)) at 1.
  unfold R.v612, N.v612.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_613 (s : N.State) (i : N.Inputs) :
  R.v613 (state s) (inputs i) = Zmod.unsigned (N.v613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v613 s i)) at 1.
  unfold R.v613, N.v613.
  rewrite ?node_612.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r200_nr_5F200.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r200_nr_5F200 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_614 (s : N.State) (i : N.Inputs) :
  R.v614 (state s) (inputs i) = Zmod.unsigned (N.v614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v614 s i)) at 1.
  unfold R.v614, N.v614.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_615 (s : N.State) (i : N.Inputs) :
  R.v615 (state s) (inputs i) = Zmod.unsigned (N.v615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v615 s i)) at 1.
  unfold R.v615, N.v615.
  rewrite ?node_614.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r201_nr_5F201.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r201_nr_5F201 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_616 (s : N.State) (i : N.Inputs) :
  R.v616 (state s) (inputs i) = Zmod.unsigned (N.v616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v616 s i)) at 1.
  unfold R.v616, N.v616.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_617 (s : N.State) (i : N.Inputs) :
  R.v617 (state s) (inputs i) = Zmod.unsigned (N.v617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v617 s i)) at 1.
  unfold R.v617, N.v617.
  rewrite ?node_616.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r202_nr_5F202.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r202_nr_5F202 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_618 (s : N.State) (i : N.Inputs) :
  R.v618 (state s) (inputs i) = Zmod.unsigned (N.v618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v618 s i)) at 1.
  unfold R.v618, N.v618.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_619 (s : N.State) (i : N.Inputs) :
  R.v619 (state s) (inputs i) = Zmod.unsigned (N.v619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v619 s i)) at 1.
  unfold R.v619, N.v619.
  rewrite ?node_618.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r203_nr_5F203.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r203_nr_5F203 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_620 (s : N.State) (i : N.Inputs) :
  R.v620 (state s) (inputs i) = Zmod.unsigned (N.v620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v620 s i)) at 1.
  unfold R.v620, N.v620.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_621 (s : N.State) (i : N.Inputs) :
  R.v621 (state s) (inputs i) = Zmod.unsigned (N.v621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v621 s i)) at 1.
  unfold R.v621, N.v621.
  rewrite ?node_620.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r204_nr_5F204.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r204_nr_5F204 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_622 (s : N.State) (i : N.Inputs) :
  R.v622 (state s) (inputs i) = Zmod.unsigned (N.v622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v622 s i)) at 1.
  unfold R.v622, N.v622.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_623 (s : N.State) (i : N.Inputs) :
  R.v623 (state s) (inputs i) = Zmod.unsigned (N.v623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v623 s i)) at 1.
  unfold R.v623, N.v623.
  rewrite ?node_622.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r205_nr_5F205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r205_nr_5F205 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_624 (s : N.State) (i : N.Inputs) :
  R.v624 (state s) (inputs i) = Zmod.unsigned (N.v624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v624 s i)) at 1.
  unfold R.v624, N.v624.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_625 (s : N.State) (i : N.Inputs) :
  R.v625 (state s) (inputs i) = Zmod.unsigned (N.v625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v625 s i)) at 1.
  unfold R.v625, N.v625.
  rewrite ?node_624.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r206_nr_5F206.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r206_nr_5F206 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_626 (s : N.State) (i : N.Inputs) :
  R.v626 (state s) (inputs i) = Zmod.unsigned (N.v626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v626 s i)) at 1.
  unfold R.v626, N.v626.
  rewrite ?node_597.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_627 (s : N.State) (i : N.Inputs) :
  R.v627 (state s) (inputs i) = Zmod.unsigned (N.v627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v627 s i)) at 1.
  unfold R.v627, N.v627.
  rewrite ?node_626.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r207_nr_5F207.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r207_nr_5F207 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_628 (s : N.State) (i : N.Inputs) :
  R.v628 (state s) (inputs i) = Zmod.unsigned (N.v628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v628 s i)) at 1.
  unfold R.v628, N.v628.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_629 (s : N.State) (i : N.Inputs) :
  R.v629 (state s) (inputs i) = Zmod.unsigned (N.v629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v629 s i)) at 1.
  unfold R.v629, N.v629.
  rewrite ?node_628.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r208_nr_5F208.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r208_nr_5F208 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_630 (s : N.State) (i : N.Inputs) :
  R.v630 (state s) (inputs i) = Zmod.unsigned (N.v630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v630 s i)) at 1.
  unfold R.v630, N.v630.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_631 (s : N.State) (i : N.Inputs) :
  R.v631 (state s) (inputs i) = Zmod.unsigned (N.v631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v631 s i)) at 1.
  unfold R.v631, N.v631.
  rewrite ?node_630.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r209_nr_5F209.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r209_nr_5F209 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_632 (s : N.State) (i : N.Inputs) :
  R.v632 (state s) (inputs i) = Zmod.unsigned (N.v632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v632 s i)) at 1.
  unfold R.v632, N.v632.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_633 (s : N.State) (i : N.Inputs) :
  R.v633 (state s) (inputs i) = Zmod.unsigned (N.v633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v633 s i)) at 1.
  unfold R.v633, N.v633.
  rewrite ?node_632.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r210_nr_5F210.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r210_nr_5F210 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_634 (s : N.State) (i : N.Inputs) :
  R.v634 (state s) (inputs i) = Zmod.unsigned (N.v634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v634 s i)) at 1.
  unfold R.v634, N.v634.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_635 (s : N.State) (i : N.Inputs) :
  R.v635 (state s) (inputs i) = Zmod.unsigned (N.v635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v635 s i)) at 1.
  unfold R.v635, N.v635.
  rewrite ?node_634.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r211_nr_5F211.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r211_nr_5F211 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_636 (s : N.State) (i : N.Inputs) :
  R.v636 (state s) (inputs i) = Zmod.unsigned (N.v636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v636 s i)) at 1.
  unfold R.v636, N.v636.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_637 (s : N.State) (i : N.Inputs) :
  R.v637 (state s) (inputs i) = Zmod.unsigned (N.v637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v637 s i)) at 1.
  unfold R.v637, N.v637.
  rewrite ?node_636.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r212_nr_5F212.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r212_nr_5F212 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_638 (s : N.State) (i : N.Inputs) :
  R.v638 (state s) (inputs i) = Zmod.unsigned (N.v638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v638 s i)) at 1.
  unfold R.v638, N.v638.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_639 (s : N.State) (i : N.Inputs) :
  R.v639 (state s) (inputs i) = Zmod.unsigned (N.v639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v639 s i)) at 1.
  unfold R.v639, N.v639.
  rewrite ?node_638.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r213_nr_5F213.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r213_nr_5F213 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_640 (s : N.State) (i : N.Inputs) :
  R.v640 (state s) (inputs i) = Zmod.unsigned (N.v640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v640 s i)) at 1.
  unfold R.v640, N.v640.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_641 (s : N.State) (i : N.Inputs) :
  R.v641 (state s) (inputs i) = Zmod.unsigned (N.v641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v641 s i)) at 1.
  unfold R.v641, N.v641.
  rewrite ?node_640.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r214_nr_5F214.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r214_nr_5F214 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_642 (s : N.State) (i : N.Inputs) :
  R.v642 (state s) (inputs i) = Zmod.unsigned (N.v642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v642 s i)) at 1.
  unfold R.v642, N.v642.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_643 (s : N.State) (i : N.Inputs) :
  R.v643 (state s) (inputs i) = Zmod.unsigned (N.v643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v643 s i)) at 1.
  unfold R.v643, N.v643.
  rewrite ?node_642.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r215_nr_5F215.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r215_nr_5F215 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_644 (s : N.State) (i : N.Inputs) :
  R.v644 (state s) (inputs i) = Zmod.unsigned (N.v644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v644 s i)) at 1.
  unfold R.v644, N.v644.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_645 (s : N.State) (i : N.Inputs) :
  R.v645 (state s) (inputs i) = Zmod.unsigned (N.v645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v645 s i)) at 1.
  unfold R.v645, N.v645.
  rewrite ?node_644.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r216_nr_5F216.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r216_nr_5F216 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_646 (s : N.State) (i : N.Inputs) :
  R.v646 (state s) (inputs i) = Zmod.unsigned (N.v646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v646 s i)) at 1.
  unfold R.v646, N.v646.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_647 (s : N.State) (i : N.Inputs) :
  R.v647 (state s) (inputs i) = Zmod.unsigned (N.v647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v647 s i)) at 1.
  unfold R.v647, N.v647.
  rewrite ?node_646.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r217_nr_5F217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r217_nr_5F217 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_648 (s : N.State) (i : N.Inputs) :
  R.v648 (state s) (inputs i) = Zmod.unsigned (N.v648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v648 s i)) at 1.
  unfold R.v648, N.v648.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_649 (s : N.State) (i : N.Inputs) :
  R.v649 (state s) (inputs i) = Zmod.unsigned (N.v649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v649 s i)) at 1.
  unfold R.v649, N.v649.
  rewrite ?node_648.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r218_nr_5F218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r218_nr_5F218 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_650 (s : N.State) (i : N.Inputs) :
  R.v650 (state s) (inputs i) = Zmod.unsigned (N.v650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v650 s i)) at 1.
  unfold R.v650, N.v650.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_651 (s : N.State) (i : N.Inputs) :
  R.v651 (state s) (inputs i) = Zmod.unsigned (N.v651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v651 s i)) at 1.
  unfold R.v651, N.v651.
  rewrite ?node_650.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r219_nr_5F219.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r219_nr_5F219 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_652 (s : N.State) (i : N.Inputs) :
  R.v652 (state s) (inputs i) = Zmod.unsigned (N.v652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v652 s i)) at 1.
  unfold R.v652, N.v652.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_653 (s : N.State) (i : N.Inputs) :
  R.v653 (state s) (inputs i) = Zmod.unsigned (N.v653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v653 s i)) at 1.
  unfold R.v653, N.v653.
  rewrite ?node_652.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r220_nr_5F220.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r220_nr_5F220 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_654 (s : N.State) (i : N.Inputs) :
  R.v654 (state s) (inputs i) = Zmod.unsigned (N.v654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v654 s i)) at 1.
  unfold R.v654, N.v654.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_655 (s : N.State) (i : N.Inputs) :
  R.v655 (state s) (inputs i) = Zmod.unsigned (N.v655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v655 s i)) at 1.
  unfold R.v655, N.v655.
  unfold R.v33, N.v33.
  rewrite ?node_654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_656 (s : N.State) (i : N.Inputs) :
  R.v656 (state s) (inputs i) = Zmod.unsigned (N.v656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v656 s i)) at 1.
  unfold R.v656, N.v656.
  unfold R.v35, N.v35.
  rewrite ?node_654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_657 (s : N.State) (i : N.Inputs) :
  R.v657 (state s) (inputs i) = Zmod.unsigned (N.v657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v657 s i)) at 1.
  unfold R.v657, N.v657.
  rewrite ?node_655.
  rewrite ?node_656.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_658 (s : N.State) (i : N.Inputs) :
  R.v658 (state s) (inputs i) = Zmod.unsigned (N.v658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v658 s i)) at 1.
  unfold R.v658, N.v658.
  unfold R.v39, N.v39.
  rewrite ?node_654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_659 (s : N.State) (i : N.Inputs) :
  R.v659 (state s) (inputs i) = Zmod.unsigned (N.v659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v659 s i)) at 1.
  unfold R.v659, N.v659.
  unfold R.v42, N.v42.
  rewrite ?node_654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_660 (s : N.State) (i : N.Inputs) :
  R.v660 (state s) (inputs i) = Zmod.unsigned (N.v660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v660 s i)) at 1.
  unfold R.v660, N.v660.
  unfold R.v45, N.v45.
  rewrite ?node_654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_661 (s : N.State) (i : N.Inputs) :
  R.v661 (state s) (inputs i) = Zmod.unsigned (N.v661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v661 s i)) at 1.
  unfold R.v661, N.v661.
  unfold R.v47, N.v47.
  rewrite ?node_654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_662 (s : N.State) (i : N.Inputs) :
  R.v662 (state s) (inputs i) = Zmod.unsigned (N.v662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v662 s i)) at 1.
  unfold R.v662, N.v662.
  rewrite ?node_660.
  rewrite ?node_661.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_663 (s : N.State) (i : N.Inputs) :
  R.v663 (state s) (inputs i) = Zmod.unsigned (N.v663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v663 s i)) at 1.
  unfold R.v663, N.v663.
  unfold R.v11, N.v11.
  rewrite ?node_50.
  rewrite ?node_662.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_664 (s : N.State) (i : N.Inputs) :
  R.v664 (state s) (inputs i) = Zmod.unsigned (N.v664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v664 s i)) at 1.
  unfold R.v664, N.v664.
  rewrite ?node_44.
  rewrite ?node_659.
  rewrite ?node_663.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_665 (s : N.State) (i : N.Inputs) :
  R.v665 (state s) (inputs i) = Zmod.unsigned (N.v665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v665 s i)) at 1.
  unfold R.v665, N.v665.
  rewrite ?node_41.
  rewrite ?node_658.
  rewrite ?node_664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_666 (s : N.State) (i : N.Inputs) :
  R.v666 (state s) (inputs i) = Zmod.unsigned (N.v666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v666 s i)) at 1.
  unfold R.v666, N.v666.
  rewrite ?node_38.
  rewrite ?node_657.
  rewrite ?node_665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_667 (s : N.State) (i : N.Inputs) :
  R.v667 (state s) (inputs i) = Zmod.unsigned (N.v667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v667 s i)) at 1.
  unfold R.v667, N.v667.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_668 (s : N.State) (i : N.Inputs) :
  R.v668 (state s) (inputs i) = Zmod.unsigned (N.v668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v668 s i)) at 1.
  unfold R.v668, N.v668.
  rewrite ?node_667.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r221_nr_5F221.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r221_nr_5F221 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_669 (s : N.State) (i : N.Inputs) :
  R.v669 (state s) (inputs i) = Zmod.unsigned (N.v669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v669 s i)) at 1.
  unfold R.v669, N.v669.
  unfold R.v6, N.v6.
  rewrite ?node_658.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_670 (s : N.State) (i : N.Inputs) :
  R.v670 (state s) (inputs i) = Zmod.unsigned (N.v670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v670 s i)) at 1.
  unfold R.v670, N.v670.
  unfold R.v19, N.v19.
  rewrite ?node_657.
  rewrite ?node_669.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_671 (s : N.State) (i : N.Inputs) :
  R.v671 (state s) (inputs i) = Zmod.unsigned (N.v671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v671 s i)) at 1.
  unfold R.v671, N.v671.
  rewrite ?node_670.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_672 (s : N.State) (i : N.Inputs) :
  R.v672 (state s) (inputs i) = Zmod.unsigned (N.v672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v672 s i)) at 1.
  unfold R.v672, N.v672.
  rewrite ?node_671.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r222_nr_5F222.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r222_nr_5F222 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_673 (s : N.State) (i : N.Inputs) :
  R.v673 (state s) (inputs i) = Zmod.unsigned (N.v673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v673 s i)) at 1.
  unfold R.v673, N.v673.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_674 (s : N.State) (i : N.Inputs) :
  R.v674 (state s) (inputs i) = Zmod.unsigned (N.v674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v674 s i)) at 1.
  unfold R.v674, N.v674.
  rewrite ?node_673.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r223_nr_5F223.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r223_nr_5F223 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_675 (s : N.State) (i : N.Inputs) :
  R.v675 (state s) (inputs i) = Zmod.unsigned (N.v675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v675 s i)) at 1.
  unfold R.v675, N.v675.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_676 (s : N.State) (i : N.Inputs) :
  R.v676 (state s) (inputs i) = Zmod.unsigned (N.v676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v676 s i)) at 1.
  unfold R.v676, N.v676.
  rewrite ?node_675.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r224_nr_5F224.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r224_nr_5F224 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_677 (s : N.State) (i : N.Inputs) :
  R.v677 (state s) (inputs i) = Zmod.unsigned (N.v677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v677 s i)) at 1.
  unfold R.v677, N.v677.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_678 (s : N.State) (i : N.Inputs) :
  R.v678 (state s) (inputs i) = Zmod.unsigned (N.v678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v678 s i)) at 1.
  unfold R.v678, N.v678.
  rewrite ?node_677.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r225_nr_5F225.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r225_nr_5F225 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_679 (s : N.State) (i : N.Inputs) :
  R.v679 (state s) (inputs i) = Zmod.unsigned (N.v679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v679 s i)) at 1.
  unfold R.v679, N.v679.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_680 (s : N.State) (i : N.Inputs) :
  R.v680 (state s) (inputs i) = Zmod.unsigned (N.v680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v680 s i)) at 1.
  unfold R.v680, N.v680.
  rewrite ?node_679.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r226_nr_5F226.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r226_nr_5F226 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_681 (s : N.State) (i : N.Inputs) :
  R.v681 (state s) (inputs i) = Zmod.unsigned (N.v681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v681 s i)) at 1.
  unfold R.v681, N.v681.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_682 (s : N.State) (i : N.Inputs) :
  R.v682 (state s) (inputs i) = Zmod.unsigned (N.v682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v682 s i)) at 1.
  unfold R.v682, N.v682.
  rewrite ?node_681.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r227_nr_5F227.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r227_nr_5F227 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_683 (s : N.State) (i : N.Inputs) :
  R.v683 (state s) (inputs i) = Zmod.unsigned (N.v683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v683 s i)) at 1.
  unfold R.v683, N.v683.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_684 (s : N.State) (i : N.Inputs) :
  R.v684 (state s) (inputs i) = Zmod.unsigned (N.v684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v684 s i)) at 1.
  unfold R.v684, N.v684.
  rewrite ?node_683.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r228_nr_5F228.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r228_nr_5F228 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_685 (s : N.State) (i : N.Inputs) :
  R.v685 (state s) (inputs i) = Zmod.unsigned (N.v685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v685 s i)) at 1.
  unfold R.v685, N.v685.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_686 (s : N.State) (i : N.Inputs) :
  R.v686 (state s) (inputs i) = Zmod.unsigned (N.v686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v686 s i)) at 1.
  unfold R.v686, N.v686.
  rewrite ?node_685.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r229_nr_5F229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r229_nr_5F229 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_687 (s : N.State) (i : N.Inputs) :
  R.v687 (state s) (inputs i) = Zmod.unsigned (N.v687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v687 s i)) at 1.
  unfold R.v687, N.v687.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_688 (s : N.State) (i : N.Inputs) :
  R.v688 (state s) (inputs i) = Zmod.unsigned (N.v688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v688 s i)) at 1.
  unfold R.v688, N.v688.
  rewrite ?node_687.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r230_nr_5F230.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r230_nr_5F230 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_689 (s : N.State) (i : N.Inputs) :
  R.v689 (state s) (inputs i) = Zmod.unsigned (N.v689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v689 s i)) at 1.
  unfold R.v689, N.v689.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_690 (s : N.State) (i : N.Inputs) :
  R.v690 (state s) (inputs i) = Zmod.unsigned (N.v690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v690 s i)) at 1.
  unfold R.v690, N.v690.
  rewrite ?node_689.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r231_nr_5F231.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r231_nr_5F231 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_691 (s : N.State) (i : N.Inputs) :
  R.v691 (state s) (inputs i) = Zmod.unsigned (N.v691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v691 s i)) at 1.
  unfold R.v691, N.v691.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_692 (s : N.State) (i : N.Inputs) :
  R.v692 (state s) (inputs i) = Zmod.unsigned (N.v692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v692 s i)) at 1.
  unfold R.v692, N.v692.
  rewrite ?node_691.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r232_nr_5F232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r232_nr_5F232 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_693 (s : N.State) (i : N.Inputs) :
  R.v693 (state s) (inputs i) = Zmod.unsigned (N.v693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v693 s i)) at 1.
  unfold R.v693, N.v693.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_694 (s : N.State) (i : N.Inputs) :
  R.v694 (state s) (inputs i) = Zmod.unsigned (N.v694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v694 s i)) at 1.
  unfold R.v694, N.v694.
  rewrite ?node_693.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r233_nr_5F233.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r233_nr_5F233 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_695 (s : N.State) (i : N.Inputs) :
  R.v695 (state s) (inputs i) = Zmod.unsigned (N.v695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v695 s i)) at 1.
  unfold R.v695, N.v695.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_696 (s : N.State) (i : N.Inputs) :
  R.v696 (state s) (inputs i) = Zmod.unsigned (N.v696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v696 s i)) at 1.
  unfold R.v696, N.v696.
  rewrite ?node_695.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r234_nr_5F234.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r234_nr_5F234 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_697 (s : N.State) (i : N.Inputs) :
  R.v697 (state s) (inputs i) = Zmod.unsigned (N.v697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v697 s i)) at 1.
  unfold R.v697, N.v697.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_698 (s : N.State) (i : N.Inputs) :
  R.v698 (state s) (inputs i) = Zmod.unsigned (N.v698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v698 s i)) at 1.
  unfold R.v698, N.v698.
  rewrite ?node_697.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r235_nr_5F235.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r235_nr_5F235 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_699 (s : N.State) (i : N.Inputs) :
  R.v699 (state s) (inputs i) = Zmod.unsigned (N.v699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v699 s i)) at 1.
  unfold R.v699, N.v699.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_700 (s : N.State) (i : N.Inputs) :
  R.v700 (state s) (inputs i) = Zmod.unsigned (N.v700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v700 s i)) at 1.
  unfold R.v700, N.v700.
  rewrite ?node_699.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r236_nr_5F236.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r236_nr_5F236 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_701 (s : N.State) (i : N.Inputs) :
  R.v701 (state s) (inputs i) = Zmod.unsigned (N.v701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v701 s i)) at 1.
  unfold R.v701, N.v701.
  rewrite ?node_670.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_702 (s : N.State) (i : N.Inputs) :
  R.v702 (state s) (inputs i) = Zmod.unsigned (N.v702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v702 s i)) at 1.
  unfold R.v702, N.v702.
  rewrite ?node_701.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r237_nr_5F237.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r237_nr_5F237 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_703 (s : N.State) (i : N.Inputs) :
  R.v703 (state s) (inputs i) = Zmod.unsigned (N.v703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v703 s i)) at 1.
  unfold R.v703, N.v703.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_704 (s : N.State) (i : N.Inputs) :
  R.v704 (state s) (inputs i) = Zmod.unsigned (N.v704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v704 s i)) at 1.
  unfold R.v704, N.v704.
  rewrite ?node_703.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r238_nr_5F238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r238_nr_5F238 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_705 (s : N.State) (i : N.Inputs) :
  R.v705 (state s) (inputs i) = Zmod.unsigned (N.v705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v705 s i)) at 1.
  unfold R.v705, N.v705.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_706 (s : N.State) (i : N.Inputs) :
  R.v706 (state s) (inputs i) = Zmod.unsigned (N.v706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v706 s i)) at 1.
  unfold R.v706, N.v706.
  rewrite ?node_705.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r239_nr_5F239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r239_nr_5F239 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_707 (s : N.State) (i : N.Inputs) :
  R.v707 (state s) (inputs i) = Zmod.unsigned (N.v707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v707 s i)) at 1.
  unfold R.v707, N.v707.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_708 (s : N.State) (i : N.Inputs) :
  R.v708 (state s) (inputs i) = Zmod.unsigned (N.v708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v708 s i)) at 1.
  unfold R.v708, N.v708.
  rewrite ?node_707.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r240_nr_5F240.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r240_nr_5F240 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_709 (s : N.State) (i : N.Inputs) :
  R.v709 (state s) (inputs i) = Zmod.unsigned (N.v709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v709 s i)) at 1.
  unfold R.v709, N.v709.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_710 (s : N.State) (i : N.Inputs) :
  R.v710 (state s) (inputs i) = Zmod.unsigned (N.v710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v710 s i)) at 1.
  unfold R.v710, N.v710.
  rewrite ?node_709.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r241_nr_5F241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r241_nr_5F241 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_711 (s : N.State) (i : N.Inputs) :
  R.v711 (state s) (inputs i) = Zmod.unsigned (N.v711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v711 s i)) at 1.
  unfold R.v711, N.v711.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_712 (s : N.State) (i : N.Inputs) :
  R.v712 (state s) (inputs i) = Zmod.unsigned (N.v712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v712 s i)) at 1.
  unfold R.v712, N.v712.
  rewrite ?node_711.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r242_nr_5F242.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r242_nr_5F242 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_713 (s : N.State) (i : N.Inputs) :
  R.v713 (state s) (inputs i) = Zmod.unsigned (N.v713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v713 s i)) at 1.
  unfold R.v713, N.v713.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_714 (s : N.State) (i : N.Inputs) :
  R.v714 (state s) (inputs i) = Zmod.unsigned (N.v714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v714 s i)) at 1.
  unfold R.v714, N.v714.
  rewrite ?node_713.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r243_nr_5F243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r243_nr_5F243 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_715 (s : N.State) (i : N.Inputs) :
  R.v715 (state s) (inputs i) = Zmod.unsigned (N.v715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v715 s i)) at 1.
  unfold R.v715, N.v715.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_716 (s : N.State) (i : N.Inputs) :
  R.v716 (state s) (inputs i) = Zmod.unsigned (N.v716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v716 s i)) at 1.
  unfold R.v716, N.v716.
  rewrite ?node_715.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r244_nr_5F244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r244_nr_5F244 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_717 (s : N.State) (i : N.Inputs) :
  R.v717 (state s) (inputs i) = Zmod.unsigned (N.v717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v717 s i)) at 1.
  unfold R.v717, N.v717.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_718 (s : N.State) (i : N.Inputs) :
  R.v718 (state s) (inputs i) = Zmod.unsigned (N.v718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v718 s i)) at 1.
  unfold R.v718, N.v718.
  rewrite ?node_717.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r245_nr_5F245.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r245_nr_5F245 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_719 (s : N.State) (i : N.Inputs) :
  R.v719 (state s) (inputs i) = Zmod.unsigned (N.v719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v719 s i)) at 1.
  unfold R.v719, N.v719.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_720 (s : N.State) (i : N.Inputs) :
  R.v720 (state s) (inputs i) = Zmod.unsigned (N.v720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v720 s i)) at 1.
  unfold R.v720, N.v720.
  rewrite ?node_719.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r246_nr_5F246.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r246_nr_5F246 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_721 (s : N.State) (i : N.Inputs) :
  R.v721 (state s) (inputs i) = Zmod.unsigned (N.v721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v721 s i)) at 1.
  unfold R.v721, N.v721.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_722 (s : N.State) (i : N.Inputs) :
  R.v722 (state s) (inputs i) = Zmod.unsigned (N.v722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v722 s i)) at 1.
  unfold R.v722, N.v722.
  rewrite ?node_721.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r247_nr_5F247.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r247_nr_5F247 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_723 (s : N.State) (i : N.Inputs) :
  R.v723 (state s) (inputs i) = Zmod.unsigned (N.v723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v723 s i)) at 1.
  unfold R.v723, N.v723.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_724 (s : N.State) (i : N.Inputs) :
  R.v724 (state s) (inputs i) = Zmod.unsigned (N.v724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v724 s i)) at 1.
  unfold R.v724, N.v724.
  rewrite ?node_723.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r248_nr_5F248.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r248_nr_5F248 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_725 (s : N.State) (i : N.Inputs) :
  R.v725 (state s) (inputs i) = Zmod.unsigned (N.v725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v725 s i)) at 1.
  unfold R.v725, N.v725.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_726 (s : N.State) (i : N.Inputs) :
  R.v726 (state s) (inputs i) = Zmod.unsigned (N.v726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v726 s i)) at 1.
  unfold R.v726, N.v726.
  rewrite ?node_725.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r249_nr_5F249.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r249_nr_5F249 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_727 (s : N.State) (i : N.Inputs) :
  R.v727 (state s) (inputs i) = Zmod.unsigned (N.v727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v727 s i)) at 1.
  unfold R.v727, N.v727.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_728 (s : N.State) (i : N.Inputs) :
  R.v728 (state s) (inputs i) = Zmod.unsigned (N.v728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v728 s i)) at 1.
  unfold R.v728, N.v728.
  rewrite ?node_727.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r250_nr_5F250.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r250_nr_5F250 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_729 (s : N.State) (i : N.Inputs) :
  R.v729 (state s) (inputs i) = Zmod.unsigned (N.v729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v729 s i)) at 1.
  unfold R.v729, N.v729.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_730 (s : N.State) (i : N.Inputs) :
  R.v730 (state s) (inputs i) = Zmod.unsigned (N.v730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v730 s i)) at 1.
  unfold R.v730, N.v730.
  rewrite ?node_729.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r251_nr_5F251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r251_nr_5F251 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_731 (s : N.State) (i : N.Inputs) :
  R.v731 (state s) (inputs i) = Zmod.unsigned (N.v731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v731 s i)) at 1.
  unfold R.v731, N.v731.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_732 (s : N.State) (i : N.Inputs) :
  R.v732 (state s) (inputs i) = Zmod.unsigned (N.v732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v732 s i)) at 1.
  unfold R.v732, N.v732.
  unfold R.v33, N.v33.
  rewrite ?node_731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_733 (s : N.State) (i : N.Inputs) :
  R.v733 (state s) (inputs i) = Zmod.unsigned (N.v733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v733 s i)) at 1.
  unfold R.v733, N.v733.
  unfold R.v35, N.v35.
  rewrite ?node_731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_734 (s : N.State) (i : N.Inputs) :
  R.v734 (state s) (inputs i) = Zmod.unsigned (N.v734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v734 s i)) at 1.
  unfold R.v734, N.v734.
  rewrite ?node_732.
  rewrite ?node_733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_735 (s : N.State) (i : N.Inputs) :
  R.v735 (state s) (inputs i) = Zmod.unsigned (N.v735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v735 s i)) at 1.
  unfold R.v735, N.v735.
  unfold R.v39, N.v39.
  rewrite ?node_731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_736 (s : N.State) (i : N.Inputs) :
  R.v736 (state s) (inputs i) = Zmod.unsigned (N.v736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v736 s i)) at 1.
  unfold R.v736, N.v736.
  unfold R.v42, N.v42.
  rewrite ?node_731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_737 (s : N.State) (i : N.Inputs) :
  R.v737 (state s) (inputs i) = Zmod.unsigned (N.v737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v737 s i)) at 1.
  unfold R.v737, N.v737.
  unfold R.v45, N.v45.
  rewrite ?node_731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_738 (s : N.State) (i : N.Inputs) :
  R.v738 (state s) (inputs i) = Zmod.unsigned (N.v738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v738 s i)) at 1.
  unfold R.v738, N.v738.
  unfold R.v47, N.v47.
  rewrite ?node_731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_739 (s : N.State) (i : N.Inputs) :
  R.v739 (state s) (inputs i) = Zmod.unsigned (N.v739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v739 s i)) at 1.
  unfold R.v739, N.v739.
  rewrite ?node_737.
  rewrite ?node_738.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_740 (s : N.State) (i : N.Inputs) :
  R.v740 (state s) (inputs i) = Zmod.unsigned (N.v740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v740 s i)) at 1.
  unfold R.v740, N.v740.
  unfold R.v11, N.v11.
  rewrite ?node_50.
  rewrite ?node_739.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_741 (s : N.State) (i : N.Inputs) :
  R.v741 (state s) (inputs i) = Zmod.unsigned (N.v741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v741 s i)) at 1.
  unfold R.v741, N.v741.
  rewrite ?node_44.
  rewrite ?node_736.
  rewrite ?node_740.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_742 (s : N.State) (i : N.Inputs) :
  R.v742 (state s) (inputs i) = Zmod.unsigned (N.v742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v742 s i)) at 1.
  unfold R.v742, N.v742.
  rewrite ?node_41.
  rewrite ?node_735.
  rewrite ?node_741.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_743 (s : N.State) (i : N.Inputs) :
  R.v743 (state s) (inputs i) = Zmod.unsigned (N.v743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v743 s i)) at 1.
  unfold R.v743, N.v743.
  rewrite ?node_38.
  rewrite ?node_734.
  rewrite ?node_742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_744 (s : N.State) (i : N.Inputs) :
  R.v744 (state s) (inputs i) = Zmod.unsigned (N.v744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v744 s i)) at 1.
  unfold R.v744, N.v744.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_745 (s : N.State) (i : N.Inputs) :
  R.v745 (state s) (inputs i) = Zmod.unsigned (N.v745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v745 s i)) at 1.
  unfold R.v745, N.v745.
  rewrite ?node_744.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r252_nr_5F252.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r252_nr_5F252 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_746 (s : N.State) (i : N.Inputs) :
  R.v746 (state s) (inputs i) = Zmod.unsigned (N.v746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v746 s i)) at 1.
  unfold R.v746, N.v746.
  unfold R.v6, N.v6.
  rewrite ?node_735.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_747 (s : N.State) (i : N.Inputs) :
  R.v747 (state s) (inputs i) = Zmod.unsigned (N.v747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v747 s i)) at 1.
  unfold R.v747, N.v747.
  unfold R.v19, N.v19.
  rewrite ?node_734.
  rewrite ?node_746.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_748 (s : N.State) (i : N.Inputs) :
  R.v748 (state s) (inputs i) = Zmod.unsigned (N.v748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v748 s i)) at 1.
  unfold R.v748, N.v748.
  rewrite ?node_747.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_749 (s : N.State) (i : N.Inputs) :
  R.v749 (state s) (inputs i) = Zmod.unsigned (N.v749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v749 s i)) at 1.
  unfold R.v749, N.v749.
  rewrite ?node_748.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r253_nr_5F253.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r253_nr_5F253 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_750 (s : N.State) (i : N.Inputs) :
  R.v750 (state s) (inputs i) = Zmod.unsigned (N.v750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v750 s i)) at 1.
  unfold R.v750, N.v750.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_751 (s : N.State) (i : N.Inputs) :
  R.v751 (state s) (inputs i) = Zmod.unsigned (N.v751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v751 s i)) at 1.
  unfold R.v751, N.v751.
  rewrite ?node_750.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r254_nr_5F254.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r254_nr_5F254 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_752 (s : N.State) (i : N.Inputs) :
  R.v752 (state s) (inputs i) = Zmod.unsigned (N.v752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v752 s i)) at 1.
  unfold R.v752, N.v752.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_753 (s : N.State) (i : N.Inputs) :
  R.v753 (state s) (inputs i) = Zmod.unsigned (N.v753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v753 s i)) at 1.
  unfold R.v753, N.v753.
  rewrite ?node_752.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r255_nr_5F255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r255_nr_5F255 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_754 (s : N.State) (i : N.Inputs) :
  R.v754 (state s) (inputs i) = Zmod.unsigned (N.v754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v754 s i)) at 1.
  unfold R.v754, N.v754.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_755 (s : N.State) (i : N.Inputs) :
  R.v755 (state s) (inputs i) = Zmod.unsigned (N.v755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v755 s i)) at 1.
  unfold R.v755, N.v755.
  rewrite ?node_754.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r256_nr_5F256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r256_nr_5F256 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_756 (s : N.State) (i : N.Inputs) :
  R.v756 (state s) (inputs i) = Zmod.unsigned (N.v756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v756 s i)) at 1.
  unfold R.v756, N.v756.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_757 (s : N.State) (i : N.Inputs) :
  R.v757 (state s) (inputs i) = Zmod.unsigned (N.v757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v757 s i)) at 1.
  unfold R.v757, N.v757.
  rewrite ?node_756.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r257_nr_5F257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r257_nr_5F257 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_758 (s : N.State) (i : N.Inputs) :
  R.v758 (state s) (inputs i) = Zmod.unsigned (N.v758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v758 s i)) at 1.
  unfold R.v758, N.v758.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_759 (s : N.State) (i : N.Inputs) :
  R.v759 (state s) (inputs i) = Zmod.unsigned (N.v759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v759 s i)) at 1.
  unfold R.v759, N.v759.
  rewrite ?node_758.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r258_nr_5F258.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r258_nr_5F258 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_760 (s : N.State) (i : N.Inputs) :
  R.v760 (state s) (inputs i) = Zmod.unsigned (N.v760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v760 s i)) at 1.
  unfold R.v760, N.v760.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_761 (s : N.State) (i : N.Inputs) :
  R.v761 (state s) (inputs i) = Zmod.unsigned (N.v761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v761 s i)) at 1.
  unfold R.v761, N.v761.
  rewrite ?node_760.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r259_nr_5F259.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r259_nr_5F259 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_762 (s : N.State) (i : N.Inputs) :
  R.v762 (state s) (inputs i) = Zmod.unsigned (N.v762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v762 s i)) at 1.
  unfold R.v762, N.v762.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_763 (s : N.State) (i : N.Inputs) :
  R.v763 (state s) (inputs i) = Zmod.unsigned (N.v763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v763 s i)) at 1.
  unfold R.v763, N.v763.
  rewrite ?node_762.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r260_nr_5F260.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r260_nr_5F260 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_764 (s : N.State) (i : N.Inputs) :
  R.v764 (state s) (inputs i) = Zmod.unsigned (N.v764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v764 s i)) at 1.
  unfold R.v764, N.v764.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_765 (s : N.State) (i : N.Inputs) :
  R.v765 (state s) (inputs i) = Zmod.unsigned (N.v765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v765 s i)) at 1.
  unfold R.v765, N.v765.
  rewrite ?node_764.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r261_nr_5F261.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r261_nr_5F261 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_766 (s : N.State) (i : N.Inputs) :
  R.v766 (state s) (inputs i) = Zmod.unsigned (N.v766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v766 s i)) at 1.
  unfold R.v766, N.v766.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_767 (s : N.State) (i : N.Inputs) :
  R.v767 (state s) (inputs i) = Zmod.unsigned (N.v767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v767 s i)) at 1.
  unfold R.v767, N.v767.
  rewrite ?node_766.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r262_nr_5F262.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r262_nr_5F262 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_768 (s : N.State) (i : N.Inputs) :
  R.v768 (state s) (inputs i) = Zmod.unsigned (N.v768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v768 s i)) at 1.
  unfold R.v768, N.v768.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_769 (s : N.State) (i : N.Inputs) :
  R.v769 (state s) (inputs i) = Zmod.unsigned (N.v769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v769 s i)) at 1.
  unfold R.v769, N.v769.
  rewrite ?node_768.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r263_nr_5F263.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r263_nr_5F263 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_770 (s : N.State) (i : N.Inputs) :
  R.v770 (state s) (inputs i) = Zmod.unsigned (N.v770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v770 s i)) at 1.
  unfold R.v770, N.v770.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_771 (s : N.State) (i : N.Inputs) :
  R.v771 (state s) (inputs i) = Zmod.unsigned (N.v771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v771 s i)) at 1.
  unfold R.v771, N.v771.
  rewrite ?node_770.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r264_nr_5F264.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r264_nr_5F264 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_772 (s : N.State) (i : N.Inputs) :
  R.v772 (state s) (inputs i) = Zmod.unsigned (N.v772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v772 s i)) at 1.
  unfold R.v772, N.v772.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_773 (s : N.State) (i : N.Inputs) :
  R.v773 (state s) (inputs i) = Zmod.unsigned (N.v773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v773 s i)) at 1.
  unfold R.v773, N.v773.
  rewrite ?node_772.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r265_nr_5F265.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r265_nr_5F265 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_774 (s : N.State) (i : N.Inputs) :
  R.v774 (state s) (inputs i) = Zmod.unsigned (N.v774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v774 s i)) at 1.
  unfold R.v774, N.v774.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_775 (s : N.State) (i : N.Inputs) :
  R.v775 (state s) (inputs i) = Zmod.unsigned (N.v775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v775 s i)) at 1.
  unfold R.v775, N.v775.
  rewrite ?node_774.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r266_nr_5F266.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r266_nr_5F266 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_776 (s : N.State) (i : N.Inputs) :
  R.v776 (state s) (inputs i) = Zmod.unsigned (N.v776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v776 s i)) at 1.
  unfold R.v776, N.v776.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_777 (s : N.State) (i : N.Inputs) :
  R.v777 (state s) (inputs i) = Zmod.unsigned (N.v777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v777 s i)) at 1.
  unfold R.v777, N.v777.
  rewrite ?node_776.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r267_nr_5F267.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r267_nr_5F267 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_778 (s : N.State) (i : N.Inputs) :
  R.v778 (state s) (inputs i) = Zmod.unsigned (N.v778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v778 s i)) at 1.
  unfold R.v778, N.v778.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_779 (s : N.State) (i : N.Inputs) :
  R.v779 (state s) (inputs i) = Zmod.unsigned (N.v779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v779 s i)) at 1.
  unfold R.v779, N.v779.
  rewrite ?node_778.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r268_nr_5F268.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r268_nr_5F268 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_780 (s : N.State) (i : N.Inputs) :
  R.v780 (state s) (inputs i) = Zmod.unsigned (N.v780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v780 s i)) at 1.
  unfold R.v780, N.v780.
  rewrite ?node_747.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_781 (s : N.State) (i : N.Inputs) :
  R.v781 (state s) (inputs i) = Zmod.unsigned (N.v781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v781 s i)) at 1.
  unfold R.v781, N.v781.
  rewrite ?node_780.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r269_nr_5F269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r269_nr_5F269 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_782 (s : N.State) (i : N.Inputs) :
  R.v782 (state s) (inputs i) = Zmod.unsigned (N.v782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v782 s i)) at 1.
  unfold R.v782, N.v782.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_783 (s : N.State) (i : N.Inputs) :
  R.v783 (state s) (inputs i) = Zmod.unsigned (N.v783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v783 s i)) at 1.
  unfold R.v783, N.v783.
  rewrite ?node_782.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r270_nr_5F270.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r270_nr_5F270 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_784 (s : N.State) (i : N.Inputs) :
  R.v784 (state s) (inputs i) = Zmod.unsigned (N.v784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v784 s i)) at 1.
  unfold R.v784, N.v784.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_785 (s : N.State) (i : N.Inputs) :
  R.v785 (state s) (inputs i) = Zmod.unsigned (N.v785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v785 s i)) at 1.
  unfold R.v785, N.v785.
  rewrite ?node_784.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r271_nr_5F271.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r271_nr_5F271 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_786 (s : N.State) (i : N.Inputs) :
  R.v786 (state s) (inputs i) = Zmod.unsigned (N.v786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v786 s i)) at 1.
  unfold R.v786, N.v786.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_787 (s : N.State) (i : N.Inputs) :
  R.v787 (state s) (inputs i) = Zmod.unsigned (N.v787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v787 s i)) at 1.
  unfold R.v787, N.v787.
  rewrite ?node_786.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r272_nr_5F272.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r272_nr_5F272 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_788 (s : N.State) (i : N.Inputs) :
  R.v788 (state s) (inputs i) = Zmod.unsigned (N.v788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v788 s i)) at 1.
  unfold R.v788, N.v788.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_789 (s : N.State) (i : N.Inputs) :
  R.v789 (state s) (inputs i) = Zmod.unsigned (N.v789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v789 s i)) at 1.
  unfold R.v789, N.v789.
  rewrite ?node_788.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r273_nr_5F273.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r273_nr_5F273 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_790 (s : N.State) (i : N.Inputs) :
  R.v790 (state s) (inputs i) = Zmod.unsigned (N.v790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v790 s i)) at 1.
  unfold R.v790, N.v790.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_791 (s : N.State) (i : N.Inputs) :
  R.v791 (state s) (inputs i) = Zmod.unsigned (N.v791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v791 s i)) at 1.
  unfold R.v791, N.v791.
  rewrite ?node_790.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r274_nr_5F274.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r274_nr_5F274 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_792 (s : N.State) (i : N.Inputs) :
  R.v792 (state s) (inputs i) = Zmod.unsigned (N.v792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v792 s i)) at 1.
  unfold R.v792, N.v792.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_793 (s : N.State) (i : N.Inputs) :
  R.v793 (state s) (inputs i) = Zmod.unsigned (N.v793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v793 s i)) at 1.
  unfold R.v793, N.v793.
  rewrite ?node_792.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r275_nr_5F275.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r275_nr_5F275 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_794 (s : N.State) (i : N.Inputs) :
  R.v794 (state s) (inputs i) = Zmod.unsigned (N.v794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v794 s i)) at 1.
  unfold R.v794, N.v794.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_795 (s : N.State) (i : N.Inputs) :
  R.v795 (state s) (inputs i) = Zmod.unsigned (N.v795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v795 s i)) at 1.
  unfold R.v795, N.v795.
  rewrite ?node_794.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r276_nr_5F276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r276_nr_5F276 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_796 (s : N.State) (i : N.Inputs) :
  R.v796 (state s) (inputs i) = Zmod.unsigned (N.v796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v796 s i)) at 1.
  unfold R.v796, N.v796.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_797 (s : N.State) (i : N.Inputs) :
  R.v797 (state s) (inputs i) = Zmod.unsigned (N.v797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v797 s i)) at 1.
  unfold R.v797, N.v797.
  rewrite ?node_796.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r277_nr_5F277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r277_nr_5F277 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_798 (s : N.State) (i : N.Inputs) :
  R.v798 (state s) (inputs i) = Zmod.unsigned (N.v798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v798 s i)) at 1.
  unfold R.v798, N.v798.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_799 (s : N.State) (i : N.Inputs) :
  R.v799 (state s) (inputs i) = Zmod.unsigned (N.v799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v799 s i)) at 1.
  unfold R.v799, N.v799.
  rewrite ?node_798.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r278_nr_5F278.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r278_nr_5F278 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_800 (s : N.State) (i : N.Inputs) :
  R.v800 (state s) (inputs i) = Zmod.unsigned (N.v800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v800 s i)) at 1.
  unfold R.v800, N.v800.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_801 (s : N.State) (i : N.Inputs) :
  R.v801 (state s) (inputs i) = Zmod.unsigned (N.v801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v801 s i)) at 1.
  unfold R.v801, N.v801.
  rewrite ?node_800.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r279_nr_5F279.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r279_nr_5F279 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_802 (s : N.State) (i : N.Inputs) :
  R.v802 (state s) (inputs i) = Zmod.unsigned (N.v802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v802 s i)) at 1.
  unfold R.v802, N.v802.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_803 (s : N.State) (i : N.Inputs) :
  R.v803 (state s) (inputs i) = Zmod.unsigned (N.v803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v803 s i)) at 1.
  unfold R.v803, N.v803.
  rewrite ?node_802.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r280_nr_5F280.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r280_nr_5F280 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_804 (s : N.State) (i : N.Inputs) :
  R.v804 (state s) (inputs i) = Zmod.unsigned (N.v804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v804 s i)) at 1.
  unfold R.v804, N.v804.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_805 (s : N.State) (i : N.Inputs) :
  R.v805 (state s) (inputs i) = Zmod.unsigned (N.v805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v805 s i)) at 1.
  unfold R.v805, N.v805.
  rewrite ?node_804.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r281_nr_5F281.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r281_nr_5F281 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_806 (s : N.State) (i : N.Inputs) :
  R.v806 (state s) (inputs i) = Zmod.unsigned (N.v806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v806 s i)) at 1.
  unfold R.v806, N.v806.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_807 (s : N.State) (i : N.Inputs) :
  R.v807 (state s) (inputs i) = Zmod.unsigned (N.v807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v807 s i)) at 1.
  unfold R.v807, N.v807.
  rewrite ?node_806.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r282_nr_5F282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r282_nr_5F282 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_808 (s : N.State) (i : N.Inputs) :
  R.v808 (state s) (inputs i) = Zmod.unsigned (N.v808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v808 s i)) at 1.
  unfold R.v808, N.v808.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_809 (s : N.State) (i : N.Inputs) :
  R.v809 (state s) (inputs i) = Zmod.unsigned (N.v809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v809 s i)) at 1.
  unfold R.v809, N.v809.
  rewrite ?node_808.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r283_nr_5F283.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r283_nr_5F283 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_810 (s : N.State) (i : N.Inputs) :
  R.v810 (state s) (inputs i) = Zmod.unsigned (N.v810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v810 s i)) at 1.
  unfold R.v810, N.v810.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_811 (s : N.State) (i : N.Inputs) :
  R.v811 (state s) (inputs i) = Zmod.unsigned (N.v811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v811 s i)) at 1.
  unfold R.v811, N.v811.
  rewrite ?node_810.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r284_nr_5F284.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r284_nr_5F284 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_812 (s : N.State) (i : N.Inputs) :
  R.v812 (state s) (inputs i) = Zmod.unsigned (N.v812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v812 s i)) at 1.
  unfold R.v812, N.v812.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_813 (s : N.State) (i : N.Inputs) :
  R.v813 (state s) (inputs i) = Zmod.unsigned (N.v813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v813 s i)) at 1.
  unfold R.v813, N.v813.
  unfold R.v33, N.v33.
  rewrite ?node_812.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_814 (s : N.State) (i : N.Inputs) :
  R.v814 (state s) (inputs i) = Zmod.unsigned (N.v814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v814 s i)) at 1.
  unfold R.v814, N.v814.
  unfold R.v35, N.v35.
  rewrite ?node_812.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_815 (s : N.State) (i : N.Inputs) :
  R.v815 (state s) (inputs i) = Zmod.unsigned (N.v815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v815 s i)) at 1.
  unfold R.v815, N.v815.
  rewrite ?node_813.
  rewrite ?node_814.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_816 (s : N.State) (i : N.Inputs) :
  R.v816 (state s) (inputs i) = Zmod.unsigned (N.v816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v816 s i)) at 1.
  unfold R.v816, N.v816.
  unfold R.v39, N.v39.
  rewrite ?node_812.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_817 (s : N.State) (i : N.Inputs) :
  R.v817 (state s) (inputs i) = Zmod.unsigned (N.v817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v817 s i)) at 1.
  unfold R.v817, N.v817.
  unfold R.v42, N.v42.
  rewrite ?node_812.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_818 (s : N.State) (i : N.Inputs) :
  R.v818 (state s) (inputs i) = Zmod.unsigned (N.v818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v818 s i)) at 1.
  unfold R.v818, N.v818.
  unfold R.v45, N.v45.
  rewrite ?node_812.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_819 (s : N.State) (i : N.Inputs) :
  R.v819 (state s) (inputs i) = Zmod.unsigned (N.v819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v819 s i)) at 1.
  unfold R.v819, N.v819.
  unfold R.v47, N.v47.
  rewrite ?node_812.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_820 (s : N.State) (i : N.Inputs) :
  R.v820 (state s) (inputs i) = Zmod.unsigned (N.v820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v820 s i)) at 1.
  unfold R.v820, N.v820.
  rewrite ?node_818.
  rewrite ?node_819.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_821 (s : N.State) (i : N.Inputs) :
  R.v821 (state s) (inputs i) = Zmod.unsigned (N.v821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v821 s i)) at 1.
  unfold R.v821, N.v821.
  unfold R.v11, N.v11.
  rewrite ?node_50.
  rewrite ?node_820.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_822 (s : N.State) (i : N.Inputs) :
  R.v822 (state s) (inputs i) = Zmod.unsigned (N.v822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v822 s i)) at 1.
  unfold R.v822, N.v822.
  rewrite ?node_44.
  rewrite ?node_817.
  rewrite ?node_821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_823 (s : N.State) (i : N.Inputs) :
  R.v823 (state s) (inputs i) = Zmod.unsigned (N.v823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v823 s i)) at 1.
  unfold R.v823, N.v823.
  rewrite ?node_41.
  rewrite ?node_816.
  rewrite ?node_822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_824 (s : N.State) (i : N.Inputs) :
  R.v824 (state s) (inputs i) = Zmod.unsigned (N.v824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v824 s i)) at 1.
  unfold R.v824, N.v824.
  rewrite ?node_38.
  rewrite ?node_815.
  rewrite ?node_823.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_825 (s : N.State) (i : N.Inputs) :
  R.v825 (state s) (inputs i) = Zmod.unsigned (N.v825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v825 s i)) at 1.
  unfold R.v825, N.v825.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_826 (s : N.State) (i : N.Inputs) :
  R.v826 (state s) (inputs i) = Zmod.unsigned (N.v826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v826 s i)) at 1.
  unfold R.v826, N.v826.
  rewrite ?node_825.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r285_nr_5F285.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r285_nr_5F285 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_827 (s : N.State) (i : N.Inputs) :
  R.v827 (state s) (inputs i) = Zmod.unsigned (N.v827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v827 s i)) at 1.
  unfold R.v827, N.v827.
  unfold R.v6, N.v6.
  rewrite ?node_816.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_828 (s : N.State) (i : N.Inputs) :
  R.v828 (state s) (inputs i) = Zmod.unsigned (N.v828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v828 s i)) at 1.
  unfold R.v828, N.v828.
  unfold R.v19, N.v19.
  rewrite ?node_815.
  rewrite ?node_827.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_829 (s : N.State) (i : N.Inputs) :
  R.v829 (state s) (inputs i) = Zmod.unsigned (N.v829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v829 s i)) at 1.
  unfold R.v829, N.v829.
  rewrite ?node_828.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_830 (s : N.State) (i : N.Inputs) :
  R.v830 (state s) (inputs i) = Zmod.unsigned (N.v830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v830 s i)) at 1.
  unfold R.v830, N.v830.
  rewrite ?node_829.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r286_nr_5F286.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r286_nr_5F286 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_831 (s : N.State) (i : N.Inputs) :
  R.v831 (state s) (inputs i) = Zmod.unsigned (N.v831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v831 s i)) at 1.
  unfold R.v831, N.v831.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_832 (s : N.State) (i : N.Inputs) :
  R.v832 (state s) (inputs i) = Zmod.unsigned (N.v832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v832 s i)) at 1.
  unfold R.v832, N.v832.
  rewrite ?node_831.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r287_nr_5F287.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r287_nr_5F287 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_833 (s : N.State) (i : N.Inputs) :
  R.v833 (state s) (inputs i) = Zmod.unsigned (N.v833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v833 s i)) at 1.
  unfold R.v833, N.v833.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_834 (s : N.State) (i : N.Inputs) :
  R.v834 (state s) (inputs i) = Zmod.unsigned (N.v834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v834 s i)) at 1.
  unfold R.v834, N.v834.
  rewrite ?node_833.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r288_nr_5F288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r288_nr_5F288 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_835 (s : N.State) (i : N.Inputs) :
  R.v835 (state s) (inputs i) = Zmod.unsigned (N.v835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v835 s i)) at 1.
  unfold R.v835, N.v835.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_836 (s : N.State) (i : N.Inputs) :
  R.v836 (state s) (inputs i) = Zmod.unsigned (N.v836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v836 s i)) at 1.
  unfold R.v836, N.v836.
  rewrite ?node_835.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r289_nr_5F289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r289_nr_5F289 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_837 (s : N.State) (i : N.Inputs) :
  R.v837 (state s) (inputs i) = Zmod.unsigned (N.v837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v837 s i)) at 1.
  unfold R.v837, N.v837.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_838 (s : N.State) (i : N.Inputs) :
  R.v838 (state s) (inputs i) = Zmod.unsigned (N.v838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v838 s i)) at 1.
  unfold R.v838, N.v838.
  rewrite ?node_837.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r290_nr_5F290.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r290_nr_5F290 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_839 (s : N.State) (i : N.Inputs) :
  R.v839 (state s) (inputs i) = Zmod.unsigned (N.v839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v839 s i)) at 1.
  unfold R.v839, N.v839.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_840 (s : N.State) (i : N.Inputs) :
  R.v840 (state s) (inputs i) = Zmod.unsigned (N.v840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v840 s i)) at 1.
  unfold R.v840, N.v840.
  rewrite ?node_839.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r291_nr_5F291.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r291_nr_5F291 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_841 (s : N.State) (i : N.Inputs) :
  R.v841 (state s) (inputs i) = Zmod.unsigned (N.v841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v841 s i)) at 1.
  unfold R.v841, N.v841.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_842 (s : N.State) (i : N.Inputs) :
  R.v842 (state s) (inputs i) = Zmod.unsigned (N.v842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v842 s i)) at 1.
  unfold R.v842, N.v842.
  rewrite ?node_841.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r292_nr_5F292.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r292_nr_5F292 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_843 (s : N.State) (i : N.Inputs) :
  R.v843 (state s) (inputs i) = Zmod.unsigned (N.v843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v843 s i)) at 1.
  unfold R.v843, N.v843.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_844 (s : N.State) (i : N.Inputs) :
  R.v844 (state s) (inputs i) = Zmod.unsigned (N.v844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v844 s i)) at 1.
  unfold R.v844, N.v844.
  rewrite ?node_843.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r293_nr_5F293.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r293_nr_5F293 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_845 (s : N.State) (i : N.Inputs) :
  R.v845 (state s) (inputs i) = Zmod.unsigned (N.v845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v845 s i)) at 1.
  unfold R.v845, N.v845.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_846 (s : N.State) (i : N.Inputs) :
  R.v846 (state s) (inputs i) = Zmod.unsigned (N.v846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v846 s i)) at 1.
  unfold R.v846, N.v846.
  rewrite ?node_845.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r294_nr_5F294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r294_nr_5F294 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_847 (s : N.State) (i : N.Inputs) :
  R.v847 (state s) (inputs i) = Zmod.unsigned (N.v847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v847 s i)) at 1.
  unfold R.v847, N.v847.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_848 (s : N.State) (i : N.Inputs) :
  R.v848 (state s) (inputs i) = Zmod.unsigned (N.v848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v848 s i)) at 1.
  unfold R.v848, N.v848.
  rewrite ?node_847.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r295_nr_5F295.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r295_nr_5F295 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_849 (s : N.State) (i : N.Inputs) :
  R.v849 (state s) (inputs i) = Zmod.unsigned (N.v849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v849 s i)) at 1.
  unfold R.v849, N.v849.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_850 (s : N.State) (i : N.Inputs) :
  R.v850 (state s) (inputs i) = Zmod.unsigned (N.v850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v850 s i)) at 1.
  unfold R.v850, N.v850.
  rewrite ?node_849.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r296_nr_5F296.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r296_nr_5F296 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_851 (s : N.State) (i : N.Inputs) :
  R.v851 (state s) (inputs i) = Zmod.unsigned (N.v851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v851 s i)) at 1.
  unfold R.v851, N.v851.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_852 (s : N.State) (i : N.Inputs) :
  R.v852 (state s) (inputs i) = Zmod.unsigned (N.v852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v852 s i)) at 1.
  unfold R.v852, N.v852.
  rewrite ?node_851.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r297_nr_5F297.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r297_nr_5F297 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_853 (s : N.State) (i : N.Inputs) :
  R.v853 (state s) (inputs i) = Zmod.unsigned (N.v853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v853 s i)) at 1.
  unfold R.v853, N.v853.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_854 (s : N.State) (i : N.Inputs) :
  R.v854 (state s) (inputs i) = Zmod.unsigned (N.v854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v854 s i)) at 1.
  unfold R.v854, N.v854.
  rewrite ?node_853.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r298_nr_5F298.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r298_nr_5F298 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_855 (s : N.State) (i : N.Inputs) :
  R.v855 (state s) (inputs i) = Zmod.unsigned (N.v855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v855 s i)) at 1.
  unfold R.v855, N.v855.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_856 (s : N.State) (i : N.Inputs) :
  R.v856 (state s) (inputs i) = Zmod.unsigned (N.v856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v856 s i)) at 1.
  unfold R.v856, N.v856.
  rewrite ?node_855.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r299_nr_5F299.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r299_nr_5F299 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_857 (s : N.State) (i : N.Inputs) :
  R.v857 (state s) (inputs i) = Zmod.unsigned (N.v857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v857 s i)) at 1.
  unfold R.v857, N.v857.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_858 (s : N.State) (i : N.Inputs) :
  R.v858 (state s) (inputs i) = Zmod.unsigned (N.v858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v858 s i)) at 1.
  unfold R.v858, N.v858.
  rewrite ?node_857.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r300_nr_5F300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r300_nr_5F300 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_859 (s : N.State) (i : N.Inputs) :
  R.v859 (state s) (inputs i) = Zmod.unsigned (N.v859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v859 s i)) at 1.
  unfold R.v859, N.v859.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_860 (s : N.State) (i : N.Inputs) :
  R.v860 (state s) (inputs i) = Zmod.unsigned (N.v860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v860 s i)) at 1.
  unfold R.v860, N.v860.
  rewrite ?node_859.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r301_nr_5F301.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r301_nr_5F301 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_861 (s : N.State) (i : N.Inputs) :
  R.v861 (state s) (inputs i) = Zmod.unsigned (N.v861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v861 s i)) at 1.
  unfold R.v861, N.v861.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_862 (s : N.State) (i : N.Inputs) :
  R.v862 (state s) (inputs i) = Zmod.unsigned (N.v862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v862 s i)) at 1.
  unfold R.v862, N.v862.
  rewrite ?node_861.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r302_nr_5F302.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r302_nr_5F302 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_863 (s : N.State) (i : N.Inputs) :
  R.v863 (state s) (inputs i) = Zmod.unsigned (N.v863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v863 s i)) at 1.
  unfold R.v863, N.v863.
  rewrite ?node_828.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_864 (s : N.State) (i : N.Inputs) :
  R.v864 (state s) (inputs i) = Zmod.unsigned (N.v864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v864 s i)) at 1.
  unfold R.v864, N.v864.
  rewrite ?node_863.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r303_nr_5F303.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r303_nr_5F303 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_865 (s : N.State) (i : N.Inputs) :
  R.v865 (state s) (inputs i) = Zmod.unsigned (N.v865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v865 s i)) at 1.
  unfold R.v865, N.v865.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_866 (s : N.State) (i : N.Inputs) :
  R.v866 (state s) (inputs i) = Zmod.unsigned (N.v866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v866 s i)) at 1.
  unfold R.v866, N.v866.
  rewrite ?node_865.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r304_nr_5F304.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r304_nr_5F304 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_867 (s : N.State) (i : N.Inputs) :
  R.v867 (state s) (inputs i) = Zmod.unsigned (N.v867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v867 s i)) at 1.
  unfold R.v867, N.v867.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_868 (s : N.State) (i : N.Inputs) :
  R.v868 (state s) (inputs i) = Zmod.unsigned (N.v868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v868 s i)) at 1.
  unfold R.v868, N.v868.
  rewrite ?node_867.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r305_nr_5F305.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r305_nr_5F305 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_869 (s : N.State) (i : N.Inputs) :
  R.v869 (state s) (inputs i) = Zmod.unsigned (N.v869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v869 s i)) at 1.
  unfold R.v869, N.v869.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_870 (s : N.State) (i : N.Inputs) :
  R.v870 (state s) (inputs i) = Zmod.unsigned (N.v870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v870 s i)) at 1.
  unfold R.v870, N.v870.
  rewrite ?node_869.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r306_nr_5F306.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r306_nr_5F306 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_871 (s : N.State) (i : N.Inputs) :
  R.v871 (state s) (inputs i) = Zmod.unsigned (N.v871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v871 s i)) at 1.
  unfold R.v871, N.v871.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_872 (s : N.State) (i : N.Inputs) :
  R.v872 (state s) (inputs i) = Zmod.unsigned (N.v872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v872 s i)) at 1.
  unfold R.v872, N.v872.
  rewrite ?node_871.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r307_nr_5F307.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r307_nr_5F307 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_873 (s : N.State) (i : N.Inputs) :
  R.v873 (state s) (inputs i) = Zmod.unsigned (N.v873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v873 s i)) at 1.
  unfold R.v873, N.v873.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_874 (s : N.State) (i : N.Inputs) :
  R.v874 (state s) (inputs i) = Zmod.unsigned (N.v874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v874 s i)) at 1.
  unfold R.v874, N.v874.
  rewrite ?node_873.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r308_nr_5F308.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r308_nr_5F308 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_875 (s : N.State) (i : N.Inputs) :
  R.v875 (state s) (inputs i) = Zmod.unsigned (N.v875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v875 s i)) at 1.
  unfold R.v875, N.v875.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_876 (s : N.State) (i : N.Inputs) :
  R.v876 (state s) (inputs i) = Zmod.unsigned (N.v876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v876 s i)) at 1.
  unfold R.v876, N.v876.
  rewrite ?node_875.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r309_nr_5F309.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r309_nr_5F309 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_877 (s : N.State) (i : N.Inputs) :
  R.v877 (state s) (inputs i) = Zmod.unsigned (N.v877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v877 s i)) at 1.
  unfold R.v877, N.v877.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_878 (s : N.State) (i : N.Inputs) :
  R.v878 (state s) (inputs i) = Zmod.unsigned (N.v878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v878 s i)) at 1.
  unfold R.v878, N.v878.
  rewrite ?node_877.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r310_nr_5F310.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r310_nr_5F310 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_879 (s : N.State) (i : N.Inputs) :
  R.v879 (state s) (inputs i) = Zmod.unsigned (N.v879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v879 s i)) at 1.
  unfold R.v879, N.v879.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_880 (s : N.State) (i : N.Inputs) :
  R.v880 (state s) (inputs i) = Zmod.unsigned (N.v880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v880 s i)) at 1.
  unfold R.v880, N.v880.
  rewrite ?node_879.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r311_nr_5F311.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r311_nr_5F311 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_881 (s : N.State) (i : N.Inputs) :
  R.v881 (state s) (inputs i) = Zmod.unsigned (N.v881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v881 s i)) at 1.
  unfold R.v881, N.v881.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_882 (s : N.State) (i : N.Inputs) :
  R.v882 (state s) (inputs i) = Zmod.unsigned (N.v882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v882 s i)) at 1.
  unfold R.v882, N.v882.
  rewrite ?node_881.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r312_nr_5F312.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r312_nr_5F312 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_883 (s : N.State) (i : N.Inputs) :
  R.v883 (state s) (inputs i) = Zmod.unsigned (N.v883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v883 s i)) at 1.
  unfold R.v883, N.v883.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_884 (s : N.State) (i : N.Inputs) :
  R.v884 (state s) (inputs i) = Zmod.unsigned (N.v884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v884 s i)) at 1.
  unfold R.v884, N.v884.
  rewrite ?node_883.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r313_nr_5F313.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r313_nr_5F313 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_885 (s : N.State) (i : N.Inputs) :
  R.v885 (state s) (inputs i) = Zmod.unsigned (N.v885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v885 s i)) at 1.
  unfold R.v885, N.v885.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_886 (s : N.State) (i : N.Inputs) :
  R.v886 (state s) (inputs i) = Zmod.unsigned (N.v886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v886 s i)) at 1.
  unfold R.v886, N.v886.
  rewrite ?node_885.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r314_nr_5F314.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r314_nr_5F314 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_887 (s : N.State) (i : N.Inputs) :
  R.v887 (state s) (inputs i) = Zmod.unsigned (N.v887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v887 s i)) at 1.
  unfold R.v887, N.v887.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_888 (s : N.State) (i : N.Inputs) :
  R.v888 (state s) (inputs i) = Zmod.unsigned (N.v888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v888 s i)) at 1.
  unfold R.v888, N.v888.
  rewrite ?node_887.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r315_nr_5F315.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r315_nr_5F315 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_889 (s : N.State) (i : N.Inputs) :
  R.v889 (state s) (inputs i) = Zmod.unsigned (N.v889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v889 s i)) at 1.
  unfold R.v889, N.v889.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_890 (s : N.State) (i : N.Inputs) :
  R.v890 (state s) (inputs i) = Zmod.unsigned (N.v890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v890 s i)) at 1.
  unfold R.v890, N.v890.
  rewrite ?node_889.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r316_nr_5F316.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r316_nr_5F316 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_891 (s : N.State) (i : N.Inputs) :
  R.v891 (state s) (inputs i) = Zmod.unsigned (N.v891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v891 s i)) at 1.
  unfold R.v891, N.v891.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_892 (s : N.State) (i : N.Inputs) :
  R.v892 (state s) (inputs i) = Zmod.unsigned (N.v892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v892 s i)) at 1.
  unfold R.v892, N.v892.
  rewrite ?node_891.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r317_nr_5F317.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r317_nr_5F317 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_893 (s : N.State) (i : N.Inputs) :
  R.v893 (state s) (inputs i) = Zmod.unsigned (N.v893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v893 s i)) at 1.
  unfold R.v893, N.v893.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_894 (s : N.State) (i : N.Inputs) :
  R.v894 (state s) (inputs i) = Zmod.unsigned (N.v894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v894 s i)) at 1.
  unfold R.v894, N.v894.
  rewrite ?node_893.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r318_nr_5F318.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r318_nr_5F318 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_895 (s : N.State) (i : N.Inputs) :
  R.v895 (state s) (inputs i) = Zmod.unsigned (N.v895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v895 s i)) at 1.
  unfold R.v895, N.v895.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_896 (s : N.State) (i : N.Inputs) :
  R.v896 (state s) (inputs i) = Zmod.unsigned (N.v896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v896 s i)) at 1.
  unfold R.v896, N.v896.
  rewrite ?node_895.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r319_nr_5F319.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r319_nr_5F319 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_897 (s : N.State) (i : N.Inputs) :
  R.v897 (state s) (inputs i) = Zmod.unsigned (N.v897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v897 s i)) at 1.
  unfold R.v897, N.v897.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_898 (s : N.State) (i : N.Inputs) :
  R.v898 (state s) (inputs i) = Zmod.unsigned (N.v898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v898 s i)) at 1.
  unfold R.v898, N.v898.
  unfold R.v33, N.v33.
  rewrite ?node_897.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_899 (s : N.State) (i : N.Inputs) :
  R.v899 (state s) (inputs i) = Zmod.unsigned (N.v899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v899 s i)) at 1.
  unfold R.v899, N.v899.
  unfold R.v35, N.v35.
  rewrite ?node_897.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_900 (s : N.State) (i : N.Inputs) :
  R.v900 (state s) (inputs i) = Zmod.unsigned (N.v900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v900 s i)) at 1.
  unfold R.v900, N.v900.
  rewrite ?node_898.
  rewrite ?node_899.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_901 (s : N.State) (i : N.Inputs) :
  R.v901 (state s) (inputs i) = Zmod.unsigned (N.v901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v901 s i)) at 1.
  unfold R.v901, N.v901.
  unfold R.v39, N.v39.
  rewrite ?node_897.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_902 (s : N.State) (i : N.Inputs) :
  R.v902 (state s) (inputs i) = Zmod.unsigned (N.v902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v902 s i)) at 1.
  unfold R.v902, N.v902.
  unfold R.v42, N.v42.
  rewrite ?node_897.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_903 (s : N.State) (i : N.Inputs) :
  R.v903 (state s) (inputs i) = Zmod.unsigned (N.v903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v903 s i)) at 1.
  unfold R.v903, N.v903.
  unfold R.v45, N.v45.
  rewrite ?node_897.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_904 (s : N.State) (i : N.Inputs) :
  R.v904 (state s) (inputs i) = Zmod.unsigned (N.v904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v904 s i)) at 1.
  unfold R.v904, N.v904.
  unfold R.v47, N.v47.
  rewrite ?node_897.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_905 (s : N.State) (i : N.Inputs) :
  R.v905 (state s) (inputs i) = Zmod.unsigned (N.v905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v905 s i)) at 1.
  unfold R.v905, N.v905.
  rewrite ?node_903.
  rewrite ?node_904.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_906 (s : N.State) (i : N.Inputs) :
  R.v906 (state s) (inputs i) = Zmod.unsigned (N.v906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v906 s i)) at 1.
  unfold R.v906, N.v906.
  unfold R.v11, N.v11.
  rewrite ?node_50.
  rewrite ?node_905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_907 (s : N.State) (i : N.Inputs) :
  R.v907 (state s) (inputs i) = Zmod.unsigned (N.v907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v907 s i)) at 1.
  unfold R.v907, N.v907.
  rewrite ?node_44.
  rewrite ?node_902.
  rewrite ?node_906.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_908 (s : N.State) (i : N.Inputs) :
  R.v908 (state s) (inputs i) = Zmod.unsigned (N.v908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v908 s i)) at 1.
  unfold R.v908, N.v908.
  rewrite ?node_41.
  rewrite ?node_901.
  rewrite ?node_907.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_909 (s : N.State) (i : N.Inputs) :
  R.v909 (state s) (inputs i) = Zmod.unsigned (N.v909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v909 s i)) at 1.
  unfold R.v909, N.v909.
  rewrite ?node_38.
  rewrite ?node_900.
  rewrite ?node_908.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_910 (s : N.State) (i : N.Inputs) :
  R.v910 (state s) (inputs i) = Zmod.unsigned (N.v910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v910 s i)) at 1.
  unfold R.v910, N.v910.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_911 (s : N.State) (i : N.Inputs) :
  R.v911 (state s) (inputs i) = Zmod.unsigned (N.v911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v911 s i)) at 1.
  unfold R.v911, N.v911.
  rewrite ?node_910.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r320_nr_5F320.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r320_nr_5F320 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_912 (s : N.State) (i : N.Inputs) :
  R.v912 (state s) (inputs i) = Zmod.unsigned (N.v912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v912 s i)) at 1.
  unfold R.v912, N.v912.
  unfold R.v6, N.v6.
  rewrite ?node_901.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_913 (s : N.State) (i : N.Inputs) :
  R.v913 (state s) (inputs i) = Zmod.unsigned (N.v913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v913 s i)) at 1.
  unfold R.v913, N.v913.
  unfold R.v19, N.v19.
  rewrite ?node_900.
  rewrite ?node_912.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_914 (s : N.State) (i : N.Inputs) :
  R.v914 (state s) (inputs i) = Zmod.unsigned (N.v914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v914 s i)) at 1.
  unfold R.v914, N.v914.
  rewrite ?node_913.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_915 (s : N.State) (i : N.Inputs) :
  R.v915 (state s) (inputs i) = Zmod.unsigned (N.v915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v915 s i)) at 1.
  unfold R.v915, N.v915.
  rewrite ?node_914.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r321_nr_5F321.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r321_nr_5F321 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_916 (s : N.State) (i : N.Inputs) :
  R.v916 (state s) (inputs i) = Zmod.unsigned (N.v916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v916 s i)) at 1.
  unfold R.v916, N.v916.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_917 (s : N.State) (i : N.Inputs) :
  R.v917 (state s) (inputs i) = Zmod.unsigned (N.v917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v917 s i)) at 1.
  unfold R.v917, N.v917.
  rewrite ?node_916.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r322_nr_5F322.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r322_nr_5F322 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_918 (s : N.State) (i : N.Inputs) :
  R.v918 (state s) (inputs i) = Zmod.unsigned (N.v918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v918 s i)) at 1.
  unfold R.v918, N.v918.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_919 (s : N.State) (i : N.Inputs) :
  R.v919 (state s) (inputs i) = Zmod.unsigned (N.v919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v919 s i)) at 1.
  unfold R.v919, N.v919.
  rewrite ?node_918.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r323_nr_5F323.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r323_nr_5F323 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_920 (s : N.State) (i : N.Inputs) :
  R.v920 (state s) (inputs i) = Zmod.unsigned (N.v920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v920 s i)) at 1.
  unfold R.v920, N.v920.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_921 (s : N.State) (i : N.Inputs) :
  R.v921 (state s) (inputs i) = Zmod.unsigned (N.v921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v921 s i)) at 1.
  unfold R.v921, N.v921.
  rewrite ?node_920.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r324_nr_5F324.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r324_nr_5F324 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_922 (s : N.State) (i : N.Inputs) :
  R.v922 (state s) (inputs i) = Zmod.unsigned (N.v922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v922 s i)) at 1.
  unfold R.v922, N.v922.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_923 (s : N.State) (i : N.Inputs) :
  R.v923 (state s) (inputs i) = Zmod.unsigned (N.v923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v923 s i)) at 1.
  unfold R.v923, N.v923.
  rewrite ?node_922.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r325_nr_5F325.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r325_nr_5F325 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_924 (s : N.State) (i : N.Inputs) :
  R.v924 (state s) (inputs i) = Zmod.unsigned (N.v924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v924 s i)) at 1.
  unfold R.v924, N.v924.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_925 (s : N.State) (i : N.Inputs) :
  R.v925 (state s) (inputs i) = Zmod.unsigned (N.v925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v925 s i)) at 1.
  unfold R.v925, N.v925.
  rewrite ?node_924.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r326_nr_5F326.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r326_nr_5F326 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_926 (s : N.State) (i : N.Inputs) :
  R.v926 (state s) (inputs i) = Zmod.unsigned (N.v926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v926 s i)) at 1.
  unfold R.v926, N.v926.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_927 (s : N.State) (i : N.Inputs) :
  R.v927 (state s) (inputs i) = Zmod.unsigned (N.v927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v927 s i)) at 1.
  unfold R.v927, N.v927.
  rewrite ?node_926.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r327_nr_5F327.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r327_nr_5F327 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_928 (s : N.State) (i : N.Inputs) :
  R.v928 (state s) (inputs i) = Zmod.unsigned (N.v928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v928 s i)) at 1.
  unfold R.v928, N.v928.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_929 (s : N.State) (i : N.Inputs) :
  R.v929 (state s) (inputs i) = Zmod.unsigned (N.v929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v929 s i)) at 1.
  unfold R.v929, N.v929.
  rewrite ?node_928.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r328_nr_5F328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r328_nr_5F328 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_930 (s : N.State) (i : N.Inputs) :
  R.v930 (state s) (inputs i) = Zmod.unsigned (N.v930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v930 s i)) at 1.
  unfold R.v930, N.v930.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_931 (s : N.State) (i : N.Inputs) :
  R.v931 (state s) (inputs i) = Zmod.unsigned (N.v931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v931 s i)) at 1.
  unfold R.v931, N.v931.
  rewrite ?node_930.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r329_nr_5F329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r329_nr_5F329 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_932 (s : N.State) (i : N.Inputs) :
  R.v932 (state s) (inputs i) = Zmod.unsigned (N.v932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v932 s i)) at 1.
  unfold R.v932, N.v932.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_933 (s : N.State) (i : N.Inputs) :
  R.v933 (state s) (inputs i) = Zmod.unsigned (N.v933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v933 s i)) at 1.
  unfold R.v933, N.v933.
  rewrite ?node_932.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r330_nr_5F330.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r330_nr_5F330 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_934 (s : N.State) (i : N.Inputs) :
  R.v934 (state s) (inputs i) = Zmod.unsigned (N.v934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v934 s i)) at 1.
  unfold R.v934, N.v934.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_935 (s : N.State) (i : N.Inputs) :
  R.v935 (state s) (inputs i) = Zmod.unsigned (N.v935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v935 s i)) at 1.
  unfold R.v935, N.v935.
  rewrite ?node_934.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r331_nr_5F331.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r331_nr_5F331 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_936 (s : N.State) (i : N.Inputs) :
  R.v936 (state s) (inputs i) = Zmod.unsigned (N.v936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v936 s i)) at 1.
  unfold R.v936, N.v936.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_937 (s : N.State) (i : N.Inputs) :
  R.v937 (state s) (inputs i) = Zmod.unsigned (N.v937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v937 s i)) at 1.
  unfold R.v937, N.v937.
  rewrite ?node_936.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r332_nr_5F332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r332_nr_5F332 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_938 (s : N.State) (i : N.Inputs) :
  R.v938 (state s) (inputs i) = Zmod.unsigned (N.v938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v938 s i)) at 1.
  unfold R.v938, N.v938.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_939 (s : N.State) (i : N.Inputs) :
  R.v939 (state s) (inputs i) = Zmod.unsigned (N.v939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v939 s i)) at 1.
  unfold R.v939, N.v939.
  rewrite ?node_938.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r333_nr_5F333.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r333_nr_5F333 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_940 (s : N.State) (i : N.Inputs) :
  R.v940 (state s) (inputs i) = Zmod.unsigned (N.v940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v940 s i)) at 1.
  unfold R.v940, N.v940.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_941 (s : N.State) (i : N.Inputs) :
  R.v941 (state s) (inputs i) = Zmod.unsigned (N.v941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v941 s i)) at 1.
  unfold R.v941, N.v941.
  rewrite ?node_940.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r334_nr_5F334.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r334_nr_5F334 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_942 (s : N.State) (i : N.Inputs) :
  R.v942 (state s) (inputs i) = Zmod.unsigned (N.v942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v942 s i)) at 1.
  unfold R.v942, N.v942.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_943 (s : N.State) (i : N.Inputs) :
  R.v943 (state s) (inputs i) = Zmod.unsigned (N.v943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v943 s i)) at 1.
  unfold R.v943, N.v943.
  rewrite ?node_942.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r335_nr_5F335.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r335_nr_5F335 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_944 (s : N.State) (i : N.Inputs) :
  R.v944 (state s) (inputs i) = Zmod.unsigned (N.v944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v944 s i)) at 1.
  unfold R.v944, N.v944.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_945 (s : N.State) (i : N.Inputs) :
  R.v945 (state s) (inputs i) = Zmod.unsigned (N.v945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v945 s i)) at 1.
  unfold R.v945, N.v945.
  rewrite ?node_944.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r336_nr_5F336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r336_nr_5F336 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_946 (s : N.State) (i : N.Inputs) :
  R.v946 (state s) (inputs i) = Zmod.unsigned (N.v946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v946 s i)) at 1.
  unfold R.v946, N.v946.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_947 (s : N.State) (i : N.Inputs) :
  R.v947 (state s) (inputs i) = Zmod.unsigned (N.v947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v947 s i)) at 1.
  unfold R.v947, N.v947.
  rewrite ?node_946.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r337_nr_5F337.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r337_nr_5F337 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_948 (s : N.State) (i : N.Inputs) :
  R.v948 (state s) (inputs i) = Zmod.unsigned (N.v948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v948 s i)) at 1.
  unfold R.v948, N.v948.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_949 (s : N.State) (i : N.Inputs) :
  R.v949 (state s) (inputs i) = Zmod.unsigned (N.v949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v949 s i)) at 1.
  unfold R.v949, N.v949.
  rewrite ?node_948.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r338_nr_5F338.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r338_nr_5F338 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_950 (s : N.State) (i : N.Inputs) :
  R.v950 (state s) (inputs i) = Zmod.unsigned (N.v950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v950 s i)) at 1.
  unfold R.v950, N.v950.
  rewrite ?node_913.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_951 (s : N.State) (i : N.Inputs) :
  R.v951 (state s) (inputs i) = Zmod.unsigned (N.v951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v951 s i)) at 1.
  unfold R.v951, N.v951.
  rewrite ?node_950.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r339_nr_5F339.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r339_nr_5F339 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_952 (s : N.State) (i : N.Inputs) :
  R.v952 (state s) (inputs i) = Zmod.unsigned (N.v952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v952 s i)) at 1.
  unfold R.v952, N.v952.
  rewrite ?node_13.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_953 (s : N.State) (i : N.Inputs) :
  R.v953 (state s) (inputs i) = Zmod.unsigned (N.v953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v953 s i)) at 1.
  unfold R.v953, N.v953.
  rewrite ?node_952.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r340_nr_5F340.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r340_nr_5F340 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_954 (s : N.State) (i : N.Inputs) :
  R.v954 (state s) (inputs i) = Zmod.unsigned (N.v954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v954 s i)) at 1.
  unfold R.v954, N.v954.
  rewrite ?node_54.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_955 (s : N.State) (i : N.Inputs) :
  R.v955 (state s) (inputs i) = Zmod.unsigned (N.v955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v955 s i)) at 1.
  unfold R.v955, N.v955.
  rewrite ?node_954.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r341_nr_5F341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r341_nr_5F341 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_956 (s : N.State) (i : N.Inputs) :
  R.v956 (state s) (inputs i) = Zmod.unsigned (N.v956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v956 s i)) at 1.
  unfold R.v956, N.v956.
  rewrite ?node_83.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_957 (s : N.State) (i : N.Inputs) :
  R.v957 (state s) (inputs i) = Zmod.unsigned (N.v957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v957 s i)) at 1.
  unfold R.v957, N.v957.
  rewrite ?node_956.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r342_nr_5F342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r342_nr_5F342 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_958 (s : N.State) (i : N.Inputs) :
  R.v958 (state s) (inputs i) = Zmod.unsigned (N.v958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v958 s i)) at 1.
  unfold R.v958, N.v958.
  rewrite ?node_116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_959 (s : N.State) (i : N.Inputs) :
  R.v959 (state s) (inputs i) = Zmod.unsigned (N.v959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v959 s i)) at 1.
  unfold R.v959, N.v959.
  rewrite ?node_958.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r343_nr_5F343.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r343_nr_5F343 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_960 (s : N.State) (i : N.Inputs) :
  R.v960 (state s) (inputs i) = Zmod.unsigned (N.v960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v960 s i)) at 1.
  unfold R.v960, N.v960.
  rewrite ?node_153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_961 (s : N.State) (i : N.Inputs) :
  R.v961 (state s) (inputs i) = Zmod.unsigned (N.v961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v961 s i)) at 1.
  unfold R.v961, N.v961.
  rewrite ?node_960.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r344_nr_5F344.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r344_nr_5F344 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_962 (s : N.State) (i : N.Inputs) :
  R.v962 (state s) (inputs i) = Zmod.unsigned (N.v962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v962 s i)) at 1.
  unfold R.v962, N.v962.
  rewrite ?node_194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_963 (s : N.State) (i : N.Inputs) :
  R.v963 (state s) (inputs i) = Zmod.unsigned (N.v963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v963 s i)) at 1.
  unfold R.v963, N.v963.
  rewrite ?node_962.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r345_nr_5F345.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r345_nr_5F345 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_964 (s : N.State) (i : N.Inputs) :
  R.v964 (state s) (inputs i) = Zmod.unsigned (N.v964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v964 s i)) at 1.
  unfold R.v964, N.v964.
  rewrite ?node_239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_965 (s : N.State) (i : N.Inputs) :
  R.v965 (state s) (inputs i) = Zmod.unsigned (N.v965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v965 s i)) at 1.
  unfold R.v965, N.v965.
  rewrite ?node_964.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r346_nr_5F346.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r346_nr_5F346 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_966 (s : N.State) (i : N.Inputs) :
  R.v966 (state s) (inputs i) = Zmod.unsigned (N.v966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v966 s i)) at 1.
  unfold R.v966, N.v966.
  rewrite ?node_288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_967 (s : N.State) (i : N.Inputs) :
  R.v967 (state s) (inputs i) = Zmod.unsigned (N.v967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v967 s i)) at 1.
  unfold R.v967, N.v967.
  rewrite ?node_966.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r347_nr_5F347.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r347_nr_5F347 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_968 (s : N.State) (i : N.Inputs) :
  R.v968 (state s) (inputs i) = Zmod.unsigned (N.v968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v968 s i)) at 1.
  unfold R.v968, N.v968.
  rewrite ?node_341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_969 (s : N.State) (i : N.Inputs) :
  R.v969 (state s) (inputs i) = Zmod.unsigned (N.v969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v969 s i)) at 1.
  unfold R.v969, N.v969.
  rewrite ?node_968.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r348_nr_5F348.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r348_nr_5F348 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_970 (s : N.State) (i : N.Inputs) :
  R.v970 (state s) (inputs i) = Zmod.unsigned (N.v970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v970 s i)) at 1.
  unfold R.v970, N.v970.
  rewrite ?node_398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_971 (s : N.State) (i : N.Inputs) :
  R.v971 (state s) (inputs i) = Zmod.unsigned (N.v971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v971 s i)) at 1.
  unfold R.v971, N.v971.
  rewrite ?node_970.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r349_nr_5F349.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r349_nr_5F349 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_972 (s : N.State) (i : N.Inputs) :
  R.v972 (state s) (inputs i) = Zmod.unsigned (N.v972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v972 s i)) at 1.
  unfold R.v972, N.v972.
  rewrite ?node_459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_973 (s : N.State) (i : N.Inputs) :
  R.v973 (state s) (inputs i) = Zmod.unsigned (N.v973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v973 s i)) at 1.
  unfold R.v973, N.v973.
  rewrite ?node_972.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r350_nr_5F350.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r350_nr_5F350 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_974 (s : N.State) (i : N.Inputs) :
  R.v974 (state s) (inputs i) = Zmod.unsigned (N.v974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v974 s i)) at 1.
  unfold R.v974, N.v974.
  rewrite ?node_524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_975 (s : N.State) (i : N.Inputs) :
  R.v975 (state s) (inputs i) = Zmod.unsigned (N.v975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v975 s i)) at 1.
  unfold R.v975, N.v975.
  rewrite ?node_974.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r351_nr_5F351.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r351_nr_5F351 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_976 (s : N.State) (i : N.Inputs) :
  R.v976 (state s) (inputs i) = Zmod.unsigned (N.v976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v976 s i)) at 1.
  unfold R.v976, N.v976.
  rewrite ?node_593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_977 (s : N.State) (i : N.Inputs) :
  R.v977 (state s) (inputs i) = Zmod.unsigned (N.v977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v977 s i)) at 1.
  unfold R.v977, N.v977.
  rewrite ?node_976.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r352_nr_5F352.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r352_nr_5F352 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_978 (s : N.State) (i : N.Inputs) :
  R.v978 (state s) (inputs i) = Zmod.unsigned (N.v978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v978 s i)) at 1.
  unfold R.v978, N.v978.
  rewrite ?node_666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_979 (s : N.State) (i : N.Inputs) :
  R.v979 (state s) (inputs i) = Zmod.unsigned (N.v979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v979 s i)) at 1.
  unfold R.v979, N.v979.
  rewrite ?node_978.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r353_nr_5F353.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r353_nr_5F353 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_980 (s : N.State) (i : N.Inputs) :
  R.v980 (state s) (inputs i) = Zmod.unsigned (N.v980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v980 s i)) at 1.
  unfold R.v980, N.v980.
  rewrite ?node_743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_981 (s : N.State) (i : N.Inputs) :
  R.v981 (state s) (inputs i) = Zmod.unsigned (N.v981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v981 s i)) at 1.
  unfold R.v981, N.v981.
  rewrite ?node_980.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r354_nr_5F354.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r354_nr_5F354 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_982 (s : N.State) (i : N.Inputs) :
  R.v982 (state s) (inputs i) = Zmod.unsigned (N.v982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v982 s i)) at 1.
  unfold R.v982, N.v982.
  rewrite ?node_824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_983 (s : N.State) (i : N.Inputs) :
  R.v983 (state s) (inputs i) = Zmod.unsigned (N.v983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v983 s i)) at 1.
  unfold R.v983, N.v983.
  rewrite ?node_982.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r355_nr_5F355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r355_nr_5F355 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_984 (s : N.State) (i : N.Inputs) :
  R.v984 (state s) (inputs i) = Zmod.unsigned (N.v984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v984 s i)) at 1.
  unfold R.v984, N.v984.
  rewrite ?node_909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_985 (s : N.State) (i : N.Inputs) :
  R.v985 (state s) (inputs i) = Zmod.unsigned (N.v985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v985 s i)) at 1.
  unfold R.v985, N.v985.
  rewrite ?node_984.
  rewrite !inputs_nio_5FregEnables_5F0.
  rewrite !state_r356_nr_5F356.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5FregEnables_5F0 i)).
  rewrite ?(bits.mod_to_Z (N.r356_nr_5F356 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_986 (s : N.State) (i : N.Inputs) :
  R.v986 (state s) (inputs i) = Zmod.unsigned (N.v986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v986 s i)) at 1.
  unfold R.v986, N.v986.
  rewrite !inputs_nio_5Fa.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nio_5Fa i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_987 (s : N.State) (i : N.Inputs) :
  R.v987 (state s) (inputs i) = Zmod.unsigned (N.v987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v987 s i)) at 1.
  unfold R.v987, N.v987.
  unfold R.v33, N.v33.
  rewrite ?node_986.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_988 (s : N.State) (i : N.Inputs) :
  R.v988 (state s) (inputs i) = Zmod.unsigned (N.v988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v988 s i)) at 1.
  unfold R.v988, N.v988.
  unfold R.v35, N.v35.
  rewrite ?node_986.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_989 (s : N.State) (i : N.Inputs) :
  R.v989 (state s) (inputs i) = Zmod.unsigned (N.v989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v989 s i)) at 1.
  unfold R.v989, N.v989.
  rewrite ?node_987.
  rewrite ?node_988.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_990 (s : N.State) (i : N.Inputs) :
  R.v990 (state s) (inputs i) = Zmod.unsigned (N.v990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v990 s i)) at 1.
  unfold R.v990, N.v990.
  unfold R.v39, N.v39.
  rewrite ?node_986.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_991 (s : N.State) (i : N.Inputs) :
  R.v991 (state s) (inputs i) = Zmod.unsigned (N.v991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v991 s i)) at 1.
  unfold R.v991, N.v991.
  unfold R.v42, N.v42.
  rewrite ?node_986.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_992 (s : N.State) (i : N.Inputs) :
  R.v992 (state s) (inputs i) = Zmod.unsigned (N.v992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v992 s i)) at 1.
  unfold R.v992, N.v992.
  unfold R.v45, N.v45.
  rewrite ?node_986.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_993 (s : N.State) (i : N.Inputs) :
  R.v993 (state s) (inputs i) = Zmod.unsigned (N.v993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v993 s i)) at 1.
  unfold R.v993, N.v993.
  unfold R.v47, N.v47.
  rewrite ?node_986.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_994 (s : N.State) (i : N.Inputs) :
  R.v994 (state s) (inputs i) = Zmod.unsigned (N.v994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v994 s i)) at 1.
  unfold R.v994, N.v994.
  rewrite ?node_992.
  rewrite ?node_993.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_995 (s : N.State) (i : N.Inputs) :
  R.v995 (state s) (inputs i) = Zmod.unsigned (N.v995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v995 s i)) at 1.
  unfold R.v995, N.v995.
  unfold R.v11, N.v11.
  rewrite ?node_50.
  rewrite ?node_994.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_996 (s : N.State) (i : N.Inputs) :
  R.v996 (state s) (inputs i) = Zmod.unsigned (N.v996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v996 s i)) at 1.
  unfold R.v996, N.v996.
  rewrite ?node_44.
  rewrite ?node_991.
  rewrite ?node_995.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_997 (s : N.State) (i : N.Inputs) :
  R.v997 (state s) (inputs i) = Zmod.unsigned (N.v997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v997 s i)) at 1.
  unfold R.v997, N.v997.
  rewrite ?node_41.
  rewrite ?node_990.
  rewrite ?node_996.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_998 (s : N.State) (i : N.Inputs) :
  R.v998 (state s) (inputs i) = Zmod.unsigned (N.v998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v998 s i)) at 1.
  unfold R.v998, N.v998.
  rewrite ?node_38.
  rewrite ?node_989.
  rewrite ?node_997.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_999 (s : N.State) (i : N.Inputs) :
  R.v999 (state s) (inputs i) = Zmod.unsigned (N.v999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v999 s i)) at 1.
  unfold R.v999, N.v999.
  rewrite ?node_998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
