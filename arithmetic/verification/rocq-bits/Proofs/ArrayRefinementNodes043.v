(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes042.
Lemma node_43000 (s : N.State) (i : N.Inputs) :
  R.v43000 (state s) (inputs i) = Zmod.unsigned (N.v43000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43000 s i)) at 1.
  unfold R.v43000, N.v43000.
  rewrite ?node_42998.
  rewrite ?node_42999.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43001 (s : N.State) (i : N.Inputs) :
  R.v43001 (state s) (inputs i) = Zmod.unsigned (N.v43001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43001 s i)) at 1.
  unfold R.v43001, N.v43001.
  unfold R.v16484, N.v16484.
  rewrite ?node_43000.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43002 (s : N.State) (i : N.Inputs) :
  R.v43002 (state s) (inputs i) = Zmod.unsigned (N.v43002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43002 s i)) at 1.
  unfold R.v43002, N.v43002.
  rewrite ?node_42995.
  rewrite ?node_42996.
  rewrite ?node_42997.
  rewrite ?node_43001.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43003 (s : N.State) (i : N.Inputs) :
  R.v43003 (state s) (inputs i) = Zmod.unsigned (N.v43003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43003 s i)) at 1.
  unfold R.v43003, N.v43003.
  unfold R.v6, N.v6.
  rewrite ?node_43002.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43004 (s : N.State) (i : N.Inputs) :
  R.v43004 (state s) (inputs i) = Zmod.unsigned (N.v43004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43004 s i)) at 1.
  unfold R.v43004, N.v43004.
  rewrite ?node_10508.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43005 (s : N.State) (i : N.Inputs) :
  R.v43005 (state s) (inputs i) = Zmod.unsigned (N.v43005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43005 s i)) at 1.
  unfold R.v43005, N.v43005.
  unfold R.v6, N.v6.
  rewrite ?node_10667.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43006 (s : N.State) (i : N.Inputs) :
  R.v43006 (state s) (inputs i) = Zmod.unsigned (N.v43006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43006 s i)) at 1.
  unfold R.v43006, N.v43006.
  unfold R.v6, N.v6.
  rewrite ?node_10722.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43007 (s : N.State) (i : N.Inputs) :
  R.v43007 (state s) (inputs i) = Zmod.unsigned (N.v43007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43007 s i)) at 1.
  unfold R.v43007, N.v43007.
  rewrite ?node_43004.
  rewrite ?node_43005.
  rewrite ?node_43006.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43008 (s : N.State) (i : N.Inputs) :
  R.v43008 (state s) (inputs i) = Zmod.unsigned (N.v43008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43008 s i)) at 1.
  unfold R.v43008, N.v43008.
  rewrite ?node_43003.
  rewrite ?node_43007.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43009 (s : N.State) (i : N.Inputs) :
  R.v43009 (state s) (inputs i) = Zmod.unsigned (N.v43009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43009 s i)) at 1.
  unfold R.v43009, N.v43009.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43010 (s : N.State) (i : N.Inputs) :
  R.v43010 (state s) (inputs i) = Zmod.unsigned (N.v43010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43010 s i)) at 1.
  unfold R.v43010, N.v43010.
  rewrite ?node_10495.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43011 (s : N.State) (i : N.Inputs) :
  R.v43011 (state s) (inputs i) = Zmod.unsigned (N.v43011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43011 s i)) at 1.
  unfold R.v43011, N.v43011.
  unfold R.v6, N.v6.
  rewrite ?node_10487.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43012 (s : N.State) (i : N.Inputs) :
  R.v43012 (state s) (inputs i) = Zmod.unsigned (N.v43012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43012 s i)) at 1.
  unfold R.v43012, N.v43012.
  unfold R.v6, N.v6.
  rewrite ?node_10480.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43013 (s : N.State) (i : N.Inputs) :
  R.v43013 (state s) (inputs i) = Zmod.unsigned (N.v43013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43013 s i)) at 1.
  unfold R.v43013, N.v43013.
  rewrite ?node_43011.
  rewrite ?node_43012.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43014 (s : N.State) (i : N.Inputs) :
  R.v43014 (state s) (inputs i) = Zmod.unsigned (N.v43014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43014 s i)) at 1.
  unfold R.v43014, N.v43014.
  unfold R.v16484, N.v16484.
  rewrite ?node_43013.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43015 (s : N.State) (i : N.Inputs) :
  R.v43015 (state s) (inputs i) = Zmod.unsigned (N.v43015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43015 s i)) at 1.
  unfold R.v43015, N.v43015.
  rewrite ?node_43010.
  rewrite ?node_43014.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43016 (s : N.State) (i : N.Inputs) :
  R.v43016 (state s) (inputs i) = Zmod.unsigned (N.v43016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43016 s i)) at 1.
  unfold R.v43016, N.v43016.
  unfold R.v6, N.v6.
  rewrite ?node_43015.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43017 (s : N.State) (i : N.Inputs) :
  R.v43017 (state s) (inputs i) = Zmod.unsigned (N.v43017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43017 s i)) at 1.
  unfold R.v43017, N.v43017.
  rewrite ?node_10496.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43018 (s : N.State) (i : N.Inputs) :
  R.v43018 (state s) (inputs i) = Zmod.unsigned (N.v43018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43018 s i)) at 1.
  unfold R.v43018, N.v43018.
  unfold R.v6, N.v6.
  rewrite ?node_10667.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43019 (s : N.State) (i : N.Inputs) :
  R.v43019 (state s) (inputs i) = Zmod.unsigned (N.v43019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43019 s i)) at 1.
  unfold R.v43019, N.v43019.
  rewrite ?node_43017.
  rewrite ?node_43018.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43020 (s : N.State) (i : N.Inputs) :
  R.v43020 (state s) (inputs i) = Zmod.unsigned (N.v43020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43020 s i)) at 1.
  unfold R.v43020, N.v43020.
  rewrite ?node_43016.
  rewrite ?node_43019.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43021 (s : N.State) (i : N.Inputs) :
  R.v43021 (state s) (inputs i) = Zmod.unsigned (N.v43021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43021 s i)) at 1.
  unfold R.v43021, N.v43021.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43022 (s : N.State) (i : N.Inputs) :
  R.v43022 (state s) (inputs i) = Zmod.unsigned (N.v43022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43022 s i)) at 1.
  unfold R.v43022, N.v43022.
  rewrite ?node_10507.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43023 (s : N.State) (i : N.Inputs) :
  R.v43023 (state s) (inputs i) = Zmod.unsigned (N.v43023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43023 s i)) at 1.
  unfold R.v43023, N.v43023.
  unfold R.v6, N.v6.
  rewrite ?node_10503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43024 (s : N.State) (i : N.Inputs) :
  R.v43024 (state s) (inputs i) = Zmod.unsigned (N.v43024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43024 s i)) at 1.
  unfold R.v43024, N.v43024.
  unfold R.v6, N.v6.
  rewrite ?node_10496.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43025 (s : N.State) (i : N.Inputs) :
  R.v43025 (state s) (inputs i) = Zmod.unsigned (N.v43025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43025 s i)) at 1.
  unfold R.v43025, N.v43025.
  rewrite ?node_43023.
  rewrite ?node_43024.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43026 (s : N.State) (i : N.Inputs) :
  R.v43026 (state s) (inputs i) = Zmod.unsigned (N.v43026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43026 s i)) at 1.
  unfold R.v43026, N.v43026.
  unfold R.v16484, N.v16484.
  rewrite ?node_43025.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43027 (s : N.State) (i : N.Inputs) :
  R.v43027 (state s) (inputs i) = Zmod.unsigned (N.v43027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43027 s i)) at 1.
  unfold R.v43027, N.v43027.
  rewrite ?node_43022.
  rewrite ?node_43026.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43028 (s : N.State) (i : N.Inputs) :
  R.v43028 (state s) (inputs i) = Zmod.unsigned (N.v43028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43028 s i)) at 1.
  unfold R.v43028, N.v43028.
  unfold R.v6, N.v6.
  rewrite ?node_43027.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43029 (s : N.State) (i : N.Inputs) :
  R.v43029 (state s) (inputs i) = Zmod.unsigned (N.v43029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43029 s i)) at 1.
  unfold R.v43029, N.v43029.
  rewrite ?node_10508.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43030 (s : N.State) (i : N.Inputs) :
  R.v43030 (state s) (inputs i) = Zmod.unsigned (N.v43030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43030 s i)) at 1.
  unfold R.v43030, N.v43030.
  unfold R.v6, N.v6.
  rewrite ?node_10722.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43031 (s : N.State) (i : N.Inputs) :
  R.v43031 (state s) (inputs i) = Zmod.unsigned (N.v43031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43031 s i)) at 1.
  unfold R.v43031, N.v43031.
  rewrite ?node_43029.
  rewrite ?node_43030.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43032 (s : N.State) (i : N.Inputs) :
  R.v43032 (state s) (inputs i) = Zmod.unsigned (N.v43032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43032 s i)) at 1.
  unfold R.v43032, N.v43032.
  rewrite ?node_43028.
  rewrite ?node_43031.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43033 (s : N.State) (i : N.Inputs) :
  R.v43033 (state s) (inputs i) = Zmod.unsigned (N.v43033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43033 s i)) at 1.
  unfold R.v43033, N.v43033.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43034 (s : N.State) (i : N.Inputs) :
  R.v43034 (state s) (inputs i) = Zmod.unsigned (N.v43034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43034 s i)) at 1.
  unfold R.v43034, N.v43034.
  rewrite ?node_10525.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43035 (s : N.State) (i : N.Inputs) :
  R.v43035 (state s) (inputs i) = Zmod.unsigned (N.v43035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43035 s i)) at 1.
  unfold R.v43035, N.v43035.
  rewrite ?node_10521.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43036 (s : N.State) (i : N.Inputs) :
  R.v43036 (state s) (inputs i) = Zmod.unsigned (N.v43036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43036 s i)) at 1.
  unfold R.v43036, N.v43036.
  rewrite ?node_10517.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43037 (s : N.State) (i : N.Inputs) :
  R.v43037 (state s) (inputs i) = Zmod.unsigned (N.v43037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43037 s i)) at 1.
  unfold R.v43037, N.v43037.
  unfold R.v6, N.v6.
  rewrite ?node_10513.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43038 (s : N.State) (i : N.Inputs) :
  R.v43038 (state s) (inputs i) = Zmod.unsigned (N.v43038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43038 s i)) at 1.
  unfold R.v43038, N.v43038.
  unfold R.v6, N.v6.
  rewrite ?node_10510.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43039 (s : N.State) (i : N.Inputs) :
  R.v43039 (state s) (inputs i) = Zmod.unsigned (N.v43039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43039 s i)) at 1.
  unfold R.v43039, N.v43039.
  rewrite ?node_43037.
  rewrite ?node_43038.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43040 (s : N.State) (i : N.Inputs) :
  R.v43040 (state s) (inputs i) = Zmod.unsigned (N.v43040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43040 s i)) at 1.
  unfold R.v43040, N.v43040.
  unfold R.v16484, N.v16484.
  rewrite ?node_43039.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43041 (s : N.State) (i : N.Inputs) :
  R.v43041 (state s) (inputs i) = Zmod.unsigned (N.v43041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43041 s i)) at 1.
  unfold R.v43041, N.v43041.
  rewrite ?node_43034.
  rewrite ?node_43035.
  rewrite ?node_43036.
  rewrite ?node_43040.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43042 (s : N.State) (i : N.Inputs) :
  R.v43042 (state s) (inputs i) = Zmod.unsigned (N.v43042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43042 s i)) at 1.
  unfold R.v43042, N.v43042.
  unfold R.v6, N.v6.
  rewrite ?node_43041.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43043 (s : N.State) (i : N.Inputs) :
  R.v43043 (state s) (inputs i) = Zmod.unsigned (N.v43043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43043 s i)) at 1.
  unfold R.v43043, N.v43043.
  rewrite ?node_10526.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43044 (s : N.State) (i : N.Inputs) :
  R.v43044 (state s) (inputs i) = Zmod.unsigned (N.v43044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43044 s i)) at 1.
  unfold R.v43044, N.v43044.
  unfold R.v6, N.v6.
  rewrite ?node_10684.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43045 (s : N.State) (i : N.Inputs) :
  R.v43045 (state s) (inputs i) = Zmod.unsigned (N.v43045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43045 s i)) at 1.
  unfold R.v43045, N.v43045.
  unfold R.v6, N.v6.
  rewrite ?node_10726.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43046 (s : N.State) (i : N.Inputs) :
  R.v43046 (state s) (inputs i) = Zmod.unsigned (N.v43046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43046 s i)) at 1.
  unfold R.v43046, N.v43046.
  rewrite ?node_43043.
  rewrite ?node_43044.
  rewrite ?node_43045.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43047 (s : N.State) (i : N.Inputs) :
  R.v43047 (state s) (inputs i) = Zmod.unsigned (N.v43047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43047 s i)) at 1.
  unfold R.v43047, N.v43047.
  rewrite ?node_43042.
  rewrite ?node_43046.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43048 (s : N.State) (i : N.Inputs) :
  R.v43048 (state s) (inputs i) = Zmod.unsigned (N.v43048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43048 s i)) at 1.
  unfold R.v43048, N.v43048.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43049 (s : N.State) (i : N.Inputs) :
  R.v43049 (state s) (inputs i) = Zmod.unsigned (N.v43049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43049 s i)) at 1.
  unfold R.v43049, N.v43049.
  rewrite ?node_10517.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43050 (s : N.State) (i : N.Inputs) :
  R.v43050 (state s) (inputs i) = Zmod.unsigned (N.v43050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43050 s i)) at 1.
  unfold R.v43050, N.v43050.
  unfold R.v6, N.v6.
  rewrite ?node_10513.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43051 (s : N.State) (i : N.Inputs) :
  R.v43051 (state s) (inputs i) = Zmod.unsigned (N.v43051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43051 s i)) at 1.
  unfold R.v43051, N.v43051.
  unfold R.v6, N.v6.
  rewrite ?node_10510.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43052 (s : N.State) (i : N.Inputs) :
  R.v43052 (state s) (inputs i) = Zmod.unsigned (N.v43052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43052 s i)) at 1.
  unfold R.v43052, N.v43052.
  rewrite ?node_43050.
  rewrite ?node_43051.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43053 (s : N.State) (i : N.Inputs) :
  R.v43053 (state s) (inputs i) = Zmod.unsigned (N.v43053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43053 s i)) at 1.
  unfold R.v43053, N.v43053.
  unfold R.v16484, N.v16484.
  rewrite ?node_43052.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43054 (s : N.State) (i : N.Inputs) :
  R.v43054 (state s) (inputs i) = Zmod.unsigned (N.v43054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43054 s i)) at 1.
  unfold R.v43054, N.v43054.
  rewrite ?node_43049.
  rewrite ?node_43053.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43055 (s : N.State) (i : N.Inputs) :
  R.v43055 (state s) (inputs i) = Zmod.unsigned (N.v43055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43055 s i)) at 1.
  unfold R.v43055, N.v43055.
  unfold R.v6, N.v6.
  rewrite ?node_43054.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43056 (s : N.State) (i : N.Inputs) :
  R.v43056 (state s) (inputs i) = Zmod.unsigned (N.v43056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43056 s i)) at 1.
  unfold R.v43056, N.v43056.
  rewrite ?node_10518.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43057 (s : N.State) (i : N.Inputs) :
  R.v43057 (state s) (inputs i) = Zmod.unsigned (N.v43057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43057 s i)) at 1.
  unfold R.v43057, N.v43057.
  unfold R.v6, N.v6.
  rewrite ?node_10684.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43058 (s : N.State) (i : N.Inputs) :
  R.v43058 (state s) (inputs i) = Zmod.unsigned (N.v43058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43058 s i)) at 1.
  unfold R.v43058, N.v43058.
  rewrite ?node_43056.
  rewrite ?node_43057.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43059 (s : N.State) (i : N.Inputs) :
  R.v43059 (state s) (inputs i) = Zmod.unsigned (N.v43059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43059 s i)) at 1.
  unfold R.v43059, N.v43059.
  rewrite ?node_43055.
  rewrite ?node_43058.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43060 (s : N.State) (i : N.Inputs) :
  R.v43060 (state s) (inputs i) = Zmod.unsigned (N.v43060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43060 s i)) at 1.
  unfold R.v43060, N.v43060.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43061 (s : N.State) (i : N.Inputs) :
  R.v43061 (state s) (inputs i) = Zmod.unsigned (N.v43061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43061 s i)) at 1.
  unfold R.v43061, N.v43061.
  rewrite ?node_10525.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43062 (s : N.State) (i : N.Inputs) :
  R.v43062 (state s) (inputs i) = Zmod.unsigned (N.v43062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43062 s i)) at 1.
  unfold R.v43062, N.v43062.
  unfold R.v6, N.v6.
  rewrite ?node_10521.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43063 (s : N.State) (i : N.Inputs) :
  R.v43063 (state s) (inputs i) = Zmod.unsigned (N.v43063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43063 s i)) at 1.
  unfold R.v43063, N.v43063.
  unfold R.v6, N.v6.
  rewrite ?node_10518.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43064 (s : N.State) (i : N.Inputs) :
  R.v43064 (state s) (inputs i) = Zmod.unsigned (N.v43064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43064 s i)) at 1.
  unfold R.v43064, N.v43064.
  rewrite ?node_43062.
  rewrite ?node_43063.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43065 (s : N.State) (i : N.Inputs) :
  R.v43065 (state s) (inputs i) = Zmod.unsigned (N.v43065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43065 s i)) at 1.
  unfold R.v43065, N.v43065.
  unfold R.v16484, N.v16484.
  rewrite ?node_43064.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43066 (s : N.State) (i : N.Inputs) :
  R.v43066 (state s) (inputs i) = Zmod.unsigned (N.v43066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43066 s i)) at 1.
  unfold R.v43066, N.v43066.
  rewrite ?node_43061.
  rewrite ?node_43065.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43067 (s : N.State) (i : N.Inputs) :
  R.v43067 (state s) (inputs i) = Zmod.unsigned (N.v43067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43067 s i)) at 1.
  unfold R.v43067, N.v43067.
  unfold R.v6, N.v6.
  rewrite ?node_43066.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43068 (s : N.State) (i : N.Inputs) :
  R.v43068 (state s) (inputs i) = Zmod.unsigned (N.v43068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43068 s i)) at 1.
  unfold R.v43068, N.v43068.
  rewrite ?node_10526.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43069 (s : N.State) (i : N.Inputs) :
  R.v43069 (state s) (inputs i) = Zmod.unsigned (N.v43069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43069 s i)) at 1.
  unfold R.v43069, N.v43069.
  unfold R.v6, N.v6.
  rewrite ?node_10726.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43070 (s : N.State) (i : N.Inputs) :
  R.v43070 (state s) (inputs i) = Zmod.unsigned (N.v43070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43070 s i)) at 1.
  unfold R.v43070, N.v43070.
  rewrite ?node_43068.
  rewrite ?node_43069.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43071 (s : N.State) (i : N.Inputs) :
  R.v43071 (state s) (inputs i) = Zmod.unsigned (N.v43071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43071 s i)) at 1.
  unfold R.v43071, N.v43071.
  rewrite ?node_43067.
  rewrite ?node_43070.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43072 (s : N.State) (i : N.Inputs) :
  R.v43072 (state s) (inputs i) = Zmod.unsigned (N.v43072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43072 s i)) at 1.
  unfold R.v43072, N.v43072.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43073 (s : N.State) (i : N.Inputs) :
  R.v43073 (state s) (inputs i) = Zmod.unsigned (N.v43073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43073 s i)) at 1.
  unfold R.v43073, N.v43073.
  rewrite ?node_10545.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43074 (s : N.State) (i : N.Inputs) :
  R.v43074 (state s) (inputs i) = Zmod.unsigned (N.v43074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43074 s i)) at 1.
  unfold R.v43074, N.v43074.
  rewrite ?node_10541.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43075 (s : N.State) (i : N.Inputs) :
  R.v43075 (state s) (inputs i) = Zmod.unsigned (N.v43075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43075 s i)) at 1.
  unfold R.v43075, N.v43075.
  rewrite ?node_10537.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43076 (s : N.State) (i : N.Inputs) :
  R.v43076 (state s) (inputs i) = Zmod.unsigned (N.v43076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43076 s i)) at 1.
  unfold R.v43076, N.v43076.
  unfold R.v6, N.v6.
  rewrite ?node_10533.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43077 (s : N.State) (i : N.Inputs) :
  R.v43077 (state s) (inputs i) = Zmod.unsigned (N.v43077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43077 s i)) at 1.
  unfold R.v43077, N.v43077.
  unfold R.v6, N.v6.
  rewrite ?node_10530.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43078 (s : N.State) (i : N.Inputs) :
  R.v43078 (state s) (inputs i) = Zmod.unsigned (N.v43078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43078 s i)) at 1.
  unfold R.v43078, N.v43078.
  rewrite ?node_43076.
  rewrite ?node_43077.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43079 (s : N.State) (i : N.Inputs) :
  R.v43079 (state s) (inputs i) = Zmod.unsigned (N.v43079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43079 s i)) at 1.
  unfold R.v43079, N.v43079.
  unfold R.v16484, N.v16484.
  rewrite ?node_43078.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43080 (s : N.State) (i : N.Inputs) :
  R.v43080 (state s) (inputs i) = Zmod.unsigned (N.v43080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43080 s i)) at 1.
  unfold R.v43080, N.v43080.
  rewrite ?node_43073.
  rewrite ?node_43074.
  rewrite ?node_43075.
  rewrite ?node_43079.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43081 (s : N.State) (i : N.Inputs) :
  R.v43081 (state s) (inputs i) = Zmod.unsigned (N.v43081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43081 s i)) at 1.
  unfold R.v43081, N.v43081.
  unfold R.v6, N.v6.
  rewrite ?node_43080.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43082 (s : N.State) (i : N.Inputs) :
  R.v43082 (state s) (inputs i) = Zmod.unsigned (N.v43082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43082 s i)) at 1.
  unfold R.v43082, N.v43082.
  rewrite ?node_10546.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43083 (s : N.State) (i : N.Inputs) :
  R.v43083 (state s) (inputs i) = Zmod.unsigned (N.v43083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43083 s i)) at 1.
  unfold R.v43083, N.v43083.
  unfold R.v6, N.v6.
  rewrite ?node_10704.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43084 (s : N.State) (i : N.Inputs) :
  R.v43084 (state s) (inputs i) = Zmod.unsigned (N.v43084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43084 s i)) at 1.
  unfold R.v43084, N.v43084.
  unfold R.v6, N.v6.
  rewrite ?node_10735.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43085 (s : N.State) (i : N.Inputs) :
  R.v43085 (state s) (inputs i) = Zmod.unsigned (N.v43085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43085 s i)) at 1.
  unfold R.v43085, N.v43085.
  rewrite ?node_43082.
  rewrite ?node_43083.
  rewrite ?node_43084.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43086 (s : N.State) (i : N.Inputs) :
  R.v43086 (state s) (inputs i) = Zmod.unsigned (N.v43086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43086 s i)) at 1.
  unfold R.v43086, N.v43086.
  rewrite ?node_43081.
  rewrite ?node_43085.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43087 (s : N.State) (i : N.Inputs) :
  R.v43087 (state s) (inputs i) = Zmod.unsigned (N.v43087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43087 s i)) at 1.
  unfold R.v43087, N.v43087.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43088 (s : N.State) (i : N.Inputs) :
  R.v43088 (state s) (inputs i) = Zmod.unsigned (N.v43088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43088 s i)) at 1.
  unfold R.v43088, N.v43088.
  rewrite ?node_10537.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43089 (s : N.State) (i : N.Inputs) :
  R.v43089 (state s) (inputs i) = Zmod.unsigned (N.v43089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43089 s i)) at 1.
  unfold R.v43089, N.v43089.
  unfold R.v6, N.v6.
  rewrite ?node_10533.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43090 (s : N.State) (i : N.Inputs) :
  R.v43090 (state s) (inputs i) = Zmod.unsigned (N.v43090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43090 s i)) at 1.
  unfold R.v43090, N.v43090.
  unfold R.v6, N.v6.
  rewrite ?node_10530.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43091 (s : N.State) (i : N.Inputs) :
  R.v43091 (state s) (inputs i) = Zmod.unsigned (N.v43091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43091 s i)) at 1.
  unfold R.v43091, N.v43091.
  rewrite ?node_43089.
  rewrite ?node_43090.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43092 (s : N.State) (i : N.Inputs) :
  R.v43092 (state s) (inputs i) = Zmod.unsigned (N.v43092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43092 s i)) at 1.
  unfold R.v43092, N.v43092.
  unfold R.v16484, N.v16484.
  rewrite ?node_43091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43093 (s : N.State) (i : N.Inputs) :
  R.v43093 (state s) (inputs i) = Zmod.unsigned (N.v43093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43093 s i)) at 1.
  unfold R.v43093, N.v43093.
  rewrite ?node_43088.
  rewrite ?node_43092.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43094 (s : N.State) (i : N.Inputs) :
  R.v43094 (state s) (inputs i) = Zmod.unsigned (N.v43094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43094 s i)) at 1.
  unfold R.v43094, N.v43094.
  unfold R.v6, N.v6.
  rewrite ?node_43093.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43095 (s : N.State) (i : N.Inputs) :
  R.v43095 (state s) (inputs i) = Zmod.unsigned (N.v43095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43095 s i)) at 1.
  unfold R.v43095, N.v43095.
  rewrite ?node_10538.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43096 (s : N.State) (i : N.Inputs) :
  R.v43096 (state s) (inputs i) = Zmod.unsigned (N.v43096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43096 s i)) at 1.
  unfold R.v43096, N.v43096.
  unfold R.v6, N.v6.
  rewrite ?node_10704.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43097 (s : N.State) (i : N.Inputs) :
  R.v43097 (state s) (inputs i) = Zmod.unsigned (N.v43097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43097 s i)) at 1.
  unfold R.v43097, N.v43097.
  rewrite ?node_43095.
  rewrite ?node_43096.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43098 (s : N.State) (i : N.Inputs) :
  R.v43098 (state s) (inputs i) = Zmod.unsigned (N.v43098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43098 s i)) at 1.
  unfold R.v43098, N.v43098.
  rewrite ?node_43094.
  rewrite ?node_43097.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43099 (s : N.State) (i : N.Inputs) :
  R.v43099 (state s) (inputs i) = Zmod.unsigned (N.v43099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43099 s i)) at 1.
  unfold R.v43099, N.v43099.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43100 (s : N.State) (i : N.Inputs) :
  R.v43100 (state s) (inputs i) = Zmod.unsigned (N.v43100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43100 s i)) at 1.
  unfold R.v43100, N.v43100.
  rewrite ?node_10545.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43101 (s : N.State) (i : N.Inputs) :
  R.v43101 (state s) (inputs i) = Zmod.unsigned (N.v43101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43101 s i)) at 1.
  unfold R.v43101, N.v43101.
  unfold R.v6, N.v6.
  rewrite ?node_10541.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43102 (s : N.State) (i : N.Inputs) :
  R.v43102 (state s) (inputs i) = Zmod.unsigned (N.v43102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43102 s i)) at 1.
  unfold R.v43102, N.v43102.
  unfold R.v6, N.v6.
  rewrite ?node_10538.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43103 (s : N.State) (i : N.Inputs) :
  R.v43103 (state s) (inputs i) = Zmod.unsigned (N.v43103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43103 s i)) at 1.
  unfold R.v43103, N.v43103.
  rewrite ?node_43101.
  rewrite ?node_43102.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43104 (s : N.State) (i : N.Inputs) :
  R.v43104 (state s) (inputs i) = Zmod.unsigned (N.v43104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43104 s i)) at 1.
  unfold R.v43104, N.v43104.
  unfold R.v16484, N.v16484.
  rewrite ?node_43103.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43105 (s : N.State) (i : N.Inputs) :
  R.v43105 (state s) (inputs i) = Zmod.unsigned (N.v43105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43105 s i)) at 1.
  unfold R.v43105, N.v43105.
  rewrite ?node_43100.
  rewrite ?node_43104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43106 (s : N.State) (i : N.Inputs) :
  R.v43106 (state s) (inputs i) = Zmod.unsigned (N.v43106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43106 s i)) at 1.
  unfold R.v43106, N.v43106.
  unfold R.v6, N.v6.
  rewrite ?node_43105.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43107 (s : N.State) (i : N.Inputs) :
  R.v43107 (state s) (inputs i) = Zmod.unsigned (N.v43107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43107 s i)) at 1.
  unfold R.v43107, N.v43107.
  rewrite ?node_10546.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43108 (s : N.State) (i : N.Inputs) :
  R.v43108 (state s) (inputs i) = Zmod.unsigned (N.v43108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43108 s i)) at 1.
  unfold R.v43108, N.v43108.
  unfold R.v6, N.v6.
  rewrite ?node_10735.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43109 (s : N.State) (i : N.Inputs) :
  R.v43109 (state s) (inputs i) = Zmod.unsigned (N.v43109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43109 s i)) at 1.
  unfold R.v43109, N.v43109.
  rewrite ?node_43107.
  rewrite ?node_43108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43110 (s : N.State) (i : N.Inputs) :
  R.v43110 (state s) (inputs i) = Zmod.unsigned (N.v43110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43110 s i)) at 1.
  unfold R.v43110, N.v43110.
  rewrite ?node_43106.
  rewrite ?node_43109.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43111 (s : N.State) (i : N.Inputs) :
  R.v43111 (state s) (inputs i) = Zmod.unsigned (N.v43111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43111 s i)) at 1.
  unfold R.v43111, N.v43111.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43112 (s : N.State) (i : N.Inputs) :
  R.v43112 (state s) (inputs i) = Zmod.unsigned (N.v43112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43112 s i)) at 1.
  unfold R.v43112, N.v43112.
  unfold R.v6, N.v6.
  rewrite ?node_10555.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43113 (s : N.State) (i : N.Inputs) :
  R.v43113 (state s) (inputs i) = Zmod.unsigned (N.v43113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43113 s i)) at 1.
  unfold R.v43113, N.v43113.
  unfold R.v6, N.v6.
  rewrite ?node_10554.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43114 (s : N.State) (i : N.Inputs) :
  R.v43114 (state s) (inputs i) = Zmod.unsigned (N.v43114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43114 s i)) at 1.
  unfold R.v43114, N.v43114.
  rewrite ?node_43112.
  rewrite ?node_43113.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43115 (s : N.State) (i : N.Inputs) :
  R.v43115 (state s) (inputs i) = Zmod.unsigned (N.v43115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43115 s i)) at 1.
  unfold R.v43115, N.v43115.
  unfold R.v16463, N.v16463.
  rewrite ?node_43114.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43116 (s : N.State) (i : N.Inputs) :
  R.v43116 (state s) (inputs i) = Zmod.unsigned (N.v43116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43116 s i)) at 1.
  unfold R.v43116, N.v43116.
  rewrite ?node_10556.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43117 (s : N.State) (i : N.Inputs) :
  R.v43117 (state s) (inputs i) = Zmod.unsigned (N.v43117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43117 s i)) at 1.
  unfold R.v43117, N.v43117.
  unfold R.v6, N.v6.
  rewrite ?node_10736.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43118 (s : N.State) (i : N.Inputs) :
  R.v43118 (state s) (inputs i) = Zmod.unsigned (N.v43118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43118 s i)) at 1.
  unfold R.v43118, N.v43118.
  rewrite ?node_43116.
  rewrite ?node_43117.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43119 (s : N.State) (i : N.Inputs) :
  R.v43119 (state s) (inputs i) = Zmod.unsigned (N.v43119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43119 s i)) at 1.
  unfold R.v43119, N.v43119.
  rewrite ?node_43115.
  rewrite ?node_43118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43120 (s : N.State) (i : N.Inputs) :
  R.v43120 (state s) (inputs i) = Zmod.unsigned (N.v43120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43120 s i)) at 1.
  unfold R.v43120, N.v43120.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43121 (s : N.State) (i : N.Inputs) :
  R.v43121 (state s) (inputs i) = Zmod.unsigned (N.v43121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43121 s i)) at 1.
  unfold R.v43121, N.v43121.
  rewrite ?node_10632.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43122 (s : N.State) (i : N.Inputs) :
  R.v43122 (state s) (inputs i) = Zmod.unsigned (N.v43122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43122 s i)) at 1.
  unfold R.v43122, N.v43122.
  rewrite ?node_10628.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43123 (s : N.State) (i : N.Inputs) :
  R.v43123 (state s) (inputs i) = Zmod.unsigned (N.v43123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43123 s i)) at 1.
  unfold R.v43123, N.v43123.
  rewrite ?node_10620.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43124 (s : N.State) (i : N.Inputs) :
  R.v43124 (state s) (inputs i) = Zmod.unsigned (N.v43124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43124 s i)) at 1.
  unfold R.v43124, N.v43124.
  unfold R.v6, N.v6.
  rewrite ?node_10612.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43125 (s : N.State) (i : N.Inputs) :
  R.v43125 (state s) (inputs i) = Zmod.unsigned (N.v43125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43125 s i)) at 1.
  unfold R.v43125, N.v43125.
  unfold R.v6, N.v6.
  rewrite ?node_10605.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43126 (s : N.State) (i : N.Inputs) :
  R.v43126 (state s) (inputs i) = Zmod.unsigned (N.v43126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43126 s i)) at 1.
  unfold R.v43126, N.v43126.
  rewrite ?node_43124.
  rewrite ?node_43125.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43127 (s : N.State) (i : N.Inputs) :
  R.v43127 (state s) (inputs i) = Zmod.unsigned (N.v43127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43127 s i)) at 1.
  unfold R.v43127, N.v43127.
  unfold R.v16484, N.v16484.
  rewrite ?node_43126.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43128 (s : N.State) (i : N.Inputs) :
  R.v43128 (state s) (inputs i) = Zmod.unsigned (N.v43128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43128 s i)) at 1.
  unfold R.v43128, N.v43128.
  rewrite ?node_43121.
  rewrite ?node_43122.
  rewrite ?node_43123.
  rewrite ?node_43127.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43129 (s : N.State) (i : N.Inputs) :
  R.v43129 (state s) (inputs i) = Zmod.unsigned (N.v43129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43129 s i)) at 1.
  unfold R.v43129, N.v43129.
  unfold R.v6, N.v6.
  rewrite ?node_43128.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43130 (s : N.State) (i : N.Inputs) :
  R.v43130 (state s) (inputs i) = Zmod.unsigned (N.v43130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43130 s i)) at 1.
  unfold R.v43130, N.v43130.
  rewrite ?node_10633.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43131 (s : N.State) (i : N.Inputs) :
  R.v43131 (state s) (inputs i) = Zmod.unsigned (N.v43131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43131 s i)) at 1.
  unfold R.v43131, N.v43131.
  unfold R.v6, N.v6.
  rewrite ?node_10793.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43132 (s : N.State) (i : N.Inputs) :
  R.v43132 (state s) (inputs i) = Zmod.unsigned (N.v43132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43132 s i)) at 1.
  unfold R.v43132, N.v43132.
  unfold R.v6, N.v6.
  rewrite ?node_10877.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43133 (s : N.State) (i : N.Inputs) :
  R.v43133 (state s) (inputs i) = Zmod.unsigned (N.v43133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43133 s i)) at 1.
  unfold R.v43133, N.v43133.
  rewrite ?node_43130.
  rewrite ?node_43131.
  rewrite ?node_43132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43134 (s : N.State) (i : N.Inputs) :
  R.v43134 (state s) (inputs i) = Zmod.unsigned (N.v43134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43134 s i)) at 1.
  unfold R.v43134, N.v43134.
  rewrite ?node_43129.
  rewrite ?node_43133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43135 (s : N.State) (i : N.Inputs) :
  R.v43135 (state s) (inputs i) = Zmod.unsigned (N.v43135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43135 s i)) at 1.
  unfold R.v43135, N.v43135.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43136 (s : N.State) (i : N.Inputs) :
  R.v43136 (state s) (inputs i) = Zmod.unsigned (N.v43136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43136 s i)) at 1.
  unfold R.v43136, N.v43136.
  rewrite ?node_10620.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43137 (s : N.State) (i : N.Inputs) :
  R.v43137 (state s) (inputs i) = Zmod.unsigned (N.v43137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43137 s i)) at 1.
  unfold R.v43137, N.v43137.
  unfold R.v6, N.v6.
  rewrite ?node_10612.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43138 (s : N.State) (i : N.Inputs) :
  R.v43138 (state s) (inputs i) = Zmod.unsigned (N.v43138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43138 s i)) at 1.
  unfold R.v43138, N.v43138.
  unfold R.v6, N.v6.
  rewrite ?node_10605.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43139 (s : N.State) (i : N.Inputs) :
  R.v43139 (state s) (inputs i) = Zmod.unsigned (N.v43139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43139 s i)) at 1.
  unfold R.v43139, N.v43139.
  rewrite ?node_43137.
  rewrite ?node_43138.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43140 (s : N.State) (i : N.Inputs) :
  R.v43140 (state s) (inputs i) = Zmod.unsigned (N.v43140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43140 s i)) at 1.
  unfold R.v43140, N.v43140.
  unfold R.v16484, N.v16484.
  rewrite ?node_43139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43141 (s : N.State) (i : N.Inputs) :
  R.v43141 (state s) (inputs i) = Zmod.unsigned (N.v43141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43141 s i)) at 1.
  unfold R.v43141, N.v43141.
  rewrite ?node_43136.
  rewrite ?node_43140.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43142 (s : N.State) (i : N.Inputs) :
  R.v43142 (state s) (inputs i) = Zmod.unsigned (N.v43142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43142 s i)) at 1.
  unfold R.v43142, N.v43142.
  unfold R.v6, N.v6.
  rewrite ?node_43141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43143 (s : N.State) (i : N.Inputs) :
  R.v43143 (state s) (inputs i) = Zmod.unsigned (N.v43143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43143 s i)) at 1.
  unfold R.v43143, N.v43143.
  rewrite ?node_10621.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43144 (s : N.State) (i : N.Inputs) :
  R.v43144 (state s) (inputs i) = Zmod.unsigned (N.v43144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43144 s i)) at 1.
  unfold R.v43144, N.v43144.
  unfold R.v6, N.v6.
  rewrite ?node_10793.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43145 (s : N.State) (i : N.Inputs) :
  R.v43145 (state s) (inputs i) = Zmod.unsigned (N.v43145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43145 s i)) at 1.
  unfold R.v43145, N.v43145.
  rewrite ?node_43143.
  rewrite ?node_43144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43146 (s : N.State) (i : N.Inputs) :
  R.v43146 (state s) (inputs i) = Zmod.unsigned (N.v43146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43146 s i)) at 1.
  unfold R.v43146, N.v43146.
  rewrite ?node_43142.
  rewrite ?node_43145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43147 (s : N.State) (i : N.Inputs) :
  R.v43147 (state s) (inputs i) = Zmod.unsigned (N.v43147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43147 s i)) at 1.
  unfold R.v43147, N.v43147.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43148 (s : N.State) (i : N.Inputs) :
  R.v43148 (state s) (inputs i) = Zmod.unsigned (N.v43148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43148 s i)) at 1.
  unfold R.v43148, N.v43148.
  rewrite ?node_10632.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43149 (s : N.State) (i : N.Inputs) :
  R.v43149 (state s) (inputs i) = Zmod.unsigned (N.v43149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43149 s i)) at 1.
  unfold R.v43149, N.v43149.
  unfold R.v6, N.v6.
  rewrite ?node_10628.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43150 (s : N.State) (i : N.Inputs) :
  R.v43150 (state s) (inputs i) = Zmod.unsigned (N.v43150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43150 s i)) at 1.
  unfold R.v43150, N.v43150.
  unfold R.v6, N.v6.
  rewrite ?node_10621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43151 (s : N.State) (i : N.Inputs) :
  R.v43151 (state s) (inputs i) = Zmod.unsigned (N.v43151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43151 s i)) at 1.
  unfold R.v43151, N.v43151.
  rewrite ?node_43149.
  rewrite ?node_43150.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43152 (s : N.State) (i : N.Inputs) :
  R.v43152 (state s) (inputs i) = Zmod.unsigned (N.v43152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43152 s i)) at 1.
  unfold R.v43152, N.v43152.
  unfold R.v16484, N.v16484.
  rewrite ?node_43151.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43153 (s : N.State) (i : N.Inputs) :
  R.v43153 (state s) (inputs i) = Zmod.unsigned (N.v43153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43153 s i)) at 1.
  unfold R.v43153, N.v43153.
  rewrite ?node_43148.
  rewrite ?node_43152.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43154 (s : N.State) (i : N.Inputs) :
  R.v43154 (state s) (inputs i) = Zmod.unsigned (N.v43154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43154 s i)) at 1.
  unfold R.v43154, N.v43154.
  unfold R.v6, N.v6.
  rewrite ?node_43153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43155 (s : N.State) (i : N.Inputs) :
  R.v43155 (state s) (inputs i) = Zmod.unsigned (N.v43155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43155 s i)) at 1.
  unfold R.v43155, N.v43155.
  rewrite ?node_10633.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43156 (s : N.State) (i : N.Inputs) :
  R.v43156 (state s) (inputs i) = Zmod.unsigned (N.v43156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43156 s i)) at 1.
  unfold R.v43156, N.v43156.
  unfold R.v6, N.v6.
  rewrite ?node_10877.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43157 (s : N.State) (i : N.Inputs) :
  R.v43157 (state s) (inputs i) = Zmod.unsigned (N.v43157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43157 s i)) at 1.
  unfold R.v43157, N.v43157.
  rewrite ?node_43155.
  rewrite ?node_43156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43158 (s : N.State) (i : N.Inputs) :
  R.v43158 (state s) (inputs i) = Zmod.unsigned (N.v43158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43158 s i)) at 1.
  unfold R.v43158, N.v43158.
  rewrite ?node_43154.
  rewrite ?node_43157.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43159 (s : N.State) (i : N.Inputs) :
  R.v43159 (state s) (inputs i) = Zmod.unsigned (N.v43159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43159 s i)) at 1.
  unfold R.v43159, N.v43159.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43160 (s : N.State) (i : N.Inputs) :
  R.v43160 (state s) (inputs i) = Zmod.unsigned (N.v43160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43160 s i)) at 1.
  unfold R.v43160, N.v43160.
  rewrite ?node_10667.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43161 (s : N.State) (i : N.Inputs) :
  R.v43161 (state s) (inputs i) = Zmod.unsigned (N.v43161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43161 s i)) at 1.
  unfold R.v43161, N.v43161.
  rewrite ?node_10663.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43162 (s : N.State) (i : N.Inputs) :
  R.v43162 (state s) (inputs i) = Zmod.unsigned (N.v43162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43162 s i)) at 1.
  unfold R.v43162, N.v43162.
  rewrite ?node_10655.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43163 (s : N.State) (i : N.Inputs) :
  R.v43163 (state s) (inputs i) = Zmod.unsigned (N.v43163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43163 s i)) at 1.
  unfold R.v43163, N.v43163.
  unfold R.v6, N.v6.
  rewrite ?node_10647.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43164 (s : N.State) (i : N.Inputs) :
  R.v43164 (state s) (inputs i) = Zmod.unsigned (N.v43164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43164 s i)) at 1.
  unfold R.v43164, N.v43164.
  unfold R.v6, N.v6.
  rewrite ?node_10640.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43165 (s : N.State) (i : N.Inputs) :
  R.v43165 (state s) (inputs i) = Zmod.unsigned (N.v43165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43165 s i)) at 1.
  unfold R.v43165, N.v43165.
  rewrite ?node_43163.
  rewrite ?node_43164.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43166 (s : N.State) (i : N.Inputs) :
  R.v43166 (state s) (inputs i) = Zmod.unsigned (N.v43166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43166 s i)) at 1.
  unfold R.v43166, N.v43166.
  unfold R.v16484, N.v16484.
  rewrite ?node_43165.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43167 (s : N.State) (i : N.Inputs) :
  R.v43167 (state s) (inputs i) = Zmod.unsigned (N.v43167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43167 s i)) at 1.
  unfold R.v43167, N.v43167.
  rewrite ?node_43160.
  rewrite ?node_43161.
  rewrite ?node_43162.
  rewrite ?node_43166.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43168 (s : N.State) (i : N.Inputs) :
  R.v43168 (state s) (inputs i) = Zmod.unsigned (N.v43168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43168 s i)) at 1.
  unfold R.v43168, N.v43168.
  unfold R.v6, N.v6.
  rewrite ?node_43167.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43169 (s : N.State) (i : N.Inputs) :
  R.v43169 (state s) (inputs i) = Zmod.unsigned (N.v43169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43169 s i)) at 1.
  unfold R.v43169, N.v43169.
  rewrite ?node_10668.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43170 (s : N.State) (i : N.Inputs) :
  R.v43170 (state s) (inputs i) = Zmod.unsigned (N.v43170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43170 s i)) at 1.
  unfold R.v43170, N.v43170.
  unfold R.v6, N.v6.
  rewrite ?node_10828.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43171 (s : N.State) (i : N.Inputs) :
  R.v43171 (state s) (inputs i) = Zmod.unsigned (N.v43171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43171 s i)) at 1.
  unfold R.v43171, N.v43171.
  unfold R.v6, N.v6.
  rewrite ?node_10881.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43172 (s : N.State) (i : N.Inputs) :
  R.v43172 (state s) (inputs i) = Zmod.unsigned (N.v43172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43172 s i)) at 1.
  unfold R.v43172, N.v43172.
  rewrite ?node_43169.
  rewrite ?node_43170.
  rewrite ?node_43171.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43173 (s : N.State) (i : N.Inputs) :
  R.v43173 (state s) (inputs i) = Zmod.unsigned (N.v43173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43173 s i)) at 1.
  unfold R.v43173, N.v43173.
  rewrite ?node_43168.
  rewrite ?node_43172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43174 (s : N.State) (i : N.Inputs) :
  R.v43174 (state s) (inputs i) = Zmod.unsigned (N.v43174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43174 s i)) at 1.
  unfold R.v43174, N.v43174.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43175 (s : N.State) (i : N.Inputs) :
  R.v43175 (state s) (inputs i) = Zmod.unsigned (N.v43175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43175 s i)) at 1.
  unfold R.v43175, N.v43175.
  rewrite ?node_10655.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43176 (s : N.State) (i : N.Inputs) :
  R.v43176 (state s) (inputs i) = Zmod.unsigned (N.v43176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43176 s i)) at 1.
  unfold R.v43176, N.v43176.
  unfold R.v6, N.v6.
  rewrite ?node_10647.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43177 (s : N.State) (i : N.Inputs) :
  R.v43177 (state s) (inputs i) = Zmod.unsigned (N.v43177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43177 s i)) at 1.
  unfold R.v43177, N.v43177.
  unfold R.v6, N.v6.
  rewrite ?node_10640.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43178 (s : N.State) (i : N.Inputs) :
  R.v43178 (state s) (inputs i) = Zmod.unsigned (N.v43178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43178 s i)) at 1.
  unfold R.v43178, N.v43178.
  rewrite ?node_43176.
  rewrite ?node_43177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43179 (s : N.State) (i : N.Inputs) :
  R.v43179 (state s) (inputs i) = Zmod.unsigned (N.v43179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43179 s i)) at 1.
  unfold R.v43179, N.v43179.
  unfold R.v16484, N.v16484.
  rewrite ?node_43178.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43180 (s : N.State) (i : N.Inputs) :
  R.v43180 (state s) (inputs i) = Zmod.unsigned (N.v43180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43180 s i)) at 1.
  unfold R.v43180, N.v43180.
  rewrite ?node_43175.
  rewrite ?node_43179.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43181 (s : N.State) (i : N.Inputs) :
  R.v43181 (state s) (inputs i) = Zmod.unsigned (N.v43181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43181 s i)) at 1.
  unfold R.v43181, N.v43181.
  unfold R.v6, N.v6.
  rewrite ?node_43180.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43182 (s : N.State) (i : N.Inputs) :
  R.v43182 (state s) (inputs i) = Zmod.unsigned (N.v43182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43182 s i)) at 1.
  unfold R.v43182, N.v43182.
  rewrite ?node_10656.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43183 (s : N.State) (i : N.Inputs) :
  R.v43183 (state s) (inputs i) = Zmod.unsigned (N.v43183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43183 s i)) at 1.
  unfold R.v43183, N.v43183.
  unfold R.v6, N.v6.
  rewrite ?node_10828.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43184 (s : N.State) (i : N.Inputs) :
  R.v43184 (state s) (inputs i) = Zmod.unsigned (N.v43184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43184 s i)) at 1.
  unfold R.v43184, N.v43184.
  rewrite ?node_43182.
  rewrite ?node_43183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43185 (s : N.State) (i : N.Inputs) :
  R.v43185 (state s) (inputs i) = Zmod.unsigned (N.v43185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43185 s i)) at 1.
  unfold R.v43185, N.v43185.
  rewrite ?node_43181.
  rewrite ?node_43184.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43186 (s : N.State) (i : N.Inputs) :
  R.v43186 (state s) (inputs i) = Zmod.unsigned (N.v43186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43186 s i)) at 1.
  unfold R.v43186, N.v43186.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43187 (s : N.State) (i : N.Inputs) :
  R.v43187 (state s) (inputs i) = Zmod.unsigned (N.v43187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43187 s i)) at 1.
  unfold R.v43187, N.v43187.
  rewrite ?node_10667.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43188 (s : N.State) (i : N.Inputs) :
  R.v43188 (state s) (inputs i) = Zmod.unsigned (N.v43188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43188 s i)) at 1.
  unfold R.v43188, N.v43188.
  unfold R.v6, N.v6.
  rewrite ?node_10663.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43189 (s : N.State) (i : N.Inputs) :
  R.v43189 (state s) (inputs i) = Zmod.unsigned (N.v43189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43189 s i)) at 1.
  unfold R.v43189, N.v43189.
  unfold R.v6, N.v6.
  rewrite ?node_10656.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43190 (s : N.State) (i : N.Inputs) :
  R.v43190 (state s) (inputs i) = Zmod.unsigned (N.v43190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43190 s i)) at 1.
  unfold R.v43190, N.v43190.
  rewrite ?node_43188.
  rewrite ?node_43189.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43191 (s : N.State) (i : N.Inputs) :
  R.v43191 (state s) (inputs i) = Zmod.unsigned (N.v43191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43191 s i)) at 1.
  unfold R.v43191, N.v43191.
  unfold R.v16484, N.v16484.
  rewrite ?node_43190.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43192 (s : N.State) (i : N.Inputs) :
  R.v43192 (state s) (inputs i) = Zmod.unsigned (N.v43192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43192 s i)) at 1.
  unfold R.v43192, N.v43192.
  rewrite ?node_43187.
  rewrite ?node_43191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43193 (s : N.State) (i : N.Inputs) :
  R.v43193 (state s) (inputs i) = Zmod.unsigned (N.v43193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43193 s i)) at 1.
  unfold R.v43193, N.v43193.
  unfold R.v6, N.v6.
  rewrite ?node_43192.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43194 (s : N.State) (i : N.Inputs) :
  R.v43194 (state s) (inputs i) = Zmod.unsigned (N.v43194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43194 s i)) at 1.
  unfold R.v43194, N.v43194.
  rewrite ?node_10668.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43195 (s : N.State) (i : N.Inputs) :
  R.v43195 (state s) (inputs i) = Zmod.unsigned (N.v43195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43195 s i)) at 1.
  unfold R.v43195, N.v43195.
  unfold R.v6, N.v6.
  rewrite ?node_10881.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43196 (s : N.State) (i : N.Inputs) :
  R.v43196 (state s) (inputs i) = Zmod.unsigned (N.v43196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43196 s i)) at 1.
  unfold R.v43196, N.v43196.
  rewrite ?node_43194.
  rewrite ?node_43195.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43197 (s : N.State) (i : N.Inputs) :
  R.v43197 (state s) (inputs i) = Zmod.unsigned (N.v43197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43197 s i)) at 1.
  unfold R.v43197, N.v43197.
  rewrite ?node_43193.
  rewrite ?node_43196.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43198 (s : N.State) (i : N.Inputs) :
  R.v43198 (state s) (inputs i) = Zmod.unsigned (N.v43198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43198 s i)) at 1.
  unfold R.v43198, N.v43198.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43199 (s : N.State) (i : N.Inputs) :
  R.v43199 (state s) (inputs i) = Zmod.unsigned (N.v43199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43199 s i)) at 1.
  unfold R.v43199, N.v43199.
  rewrite ?node_10684.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43200 (s : N.State) (i : N.Inputs) :
  R.v43200 (state s) (inputs i) = Zmod.unsigned (N.v43200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43200 s i)) at 1.
  unfold R.v43200, N.v43200.
  rewrite ?node_10680.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43201 (s : N.State) (i : N.Inputs) :
  R.v43201 (state s) (inputs i) = Zmod.unsigned (N.v43201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43201 s i)) at 1.
  unfold R.v43201, N.v43201.
  rewrite ?node_10676.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43202 (s : N.State) (i : N.Inputs) :
  R.v43202 (state s) (inputs i) = Zmod.unsigned (N.v43202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43202 s i)) at 1.
  unfold R.v43202, N.v43202.
  unfold R.v6, N.v6.
  rewrite ?node_10672.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43203 (s : N.State) (i : N.Inputs) :
  R.v43203 (state s) (inputs i) = Zmod.unsigned (N.v43203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43203 s i)) at 1.
  unfold R.v43203, N.v43203.
  unfold R.v6, N.v6.
  rewrite !state_r1220_nr_5F1220.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1220_nr_5F1220 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43204 (s : N.State) (i : N.Inputs) :
  R.v43204 (state s) (inputs i) = Zmod.unsigned (N.v43204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43204 s i)) at 1.
  unfold R.v43204, N.v43204.
  rewrite ?node_43202.
  rewrite ?node_43203.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43205 (s : N.State) (i : N.Inputs) :
  R.v43205 (state s) (inputs i) = Zmod.unsigned (N.v43205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43205 s i)) at 1.
  unfold R.v43205, N.v43205.
  unfold R.v16484, N.v16484.
  rewrite ?node_43204.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43206 (s : N.State) (i : N.Inputs) :
  R.v43206 (state s) (inputs i) = Zmod.unsigned (N.v43206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43206 s i)) at 1.
  unfold R.v43206, N.v43206.
  rewrite ?node_43199.
  rewrite ?node_43200.
  rewrite ?node_43201.
  rewrite ?node_43205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43207 (s : N.State) (i : N.Inputs) :
  R.v43207 (state s) (inputs i) = Zmod.unsigned (N.v43207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43207 s i)) at 1.
  unfold R.v43207, N.v43207.
  unfold R.v6, N.v6.
  rewrite ?node_43206.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43208 (s : N.State) (i : N.Inputs) :
  R.v43208 (state s) (inputs i) = Zmod.unsigned (N.v43208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43208 s i)) at 1.
  unfold R.v43208, N.v43208.
  rewrite ?node_10685.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43209 (s : N.State) (i : N.Inputs) :
  R.v43209 (state s) (inputs i) = Zmod.unsigned (N.v43209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43209 s i)) at 1.
  unfold R.v43209, N.v43209.
  unfold R.v6, N.v6.
  rewrite ?node_10845.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43210 (s : N.State) (i : N.Inputs) :
  R.v43210 (state s) (inputs i) = Zmod.unsigned (N.v43210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43210 s i)) at 1.
  unfold R.v43210, N.v43210.
  unfold R.v6, N.v6.
  rewrite ?node_10885.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43211 (s : N.State) (i : N.Inputs) :
  R.v43211 (state s) (inputs i) = Zmod.unsigned (N.v43211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43211 s i)) at 1.
  unfold R.v43211, N.v43211.
  rewrite ?node_43208.
  rewrite ?node_43209.
  rewrite ?node_43210.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43212 (s : N.State) (i : N.Inputs) :
  R.v43212 (state s) (inputs i) = Zmod.unsigned (N.v43212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43212 s i)) at 1.
  unfold R.v43212, N.v43212.
  rewrite ?node_43207.
  rewrite ?node_43211.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43213 (s : N.State) (i : N.Inputs) :
  R.v43213 (state s) (inputs i) = Zmod.unsigned (N.v43213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43213 s i)) at 1.
  unfold R.v43213, N.v43213.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43214 (s : N.State) (i : N.Inputs) :
  R.v43214 (state s) (inputs i) = Zmod.unsigned (N.v43214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43214 s i)) at 1.
  unfold R.v43214, N.v43214.
  rewrite ?node_10676.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43215 (s : N.State) (i : N.Inputs) :
  R.v43215 (state s) (inputs i) = Zmod.unsigned (N.v43215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43215 s i)) at 1.
  unfold R.v43215, N.v43215.
  unfold R.v6, N.v6.
  rewrite ?node_10672.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43216 (s : N.State) (i : N.Inputs) :
  R.v43216 (state s) (inputs i) = Zmod.unsigned (N.v43216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43216 s i)) at 1.
  unfold R.v43216, N.v43216.
  unfold R.v6, N.v6.
  rewrite !state_r1220_nr_5F1220.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1220_nr_5F1220 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43217 (s : N.State) (i : N.Inputs) :
  R.v43217 (state s) (inputs i) = Zmod.unsigned (N.v43217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43217 s i)) at 1.
  unfold R.v43217, N.v43217.
  rewrite ?node_43215.
  rewrite ?node_43216.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43218 (s : N.State) (i : N.Inputs) :
  R.v43218 (state s) (inputs i) = Zmod.unsigned (N.v43218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43218 s i)) at 1.
  unfold R.v43218, N.v43218.
  unfold R.v16484, N.v16484.
  rewrite ?node_43217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43219 (s : N.State) (i : N.Inputs) :
  R.v43219 (state s) (inputs i) = Zmod.unsigned (N.v43219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43219 s i)) at 1.
  unfold R.v43219, N.v43219.
  rewrite ?node_43214.
  rewrite ?node_43218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43220 (s : N.State) (i : N.Inputs) :
  R.v43220 (state s) (inputs i) = Zmod.unsigned (N.v43220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43220 s i)) at 1.
  unfold R.v43220, N.v43220.
  unfold R.v6, N.v6.
  rewrite ?node_43219.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43221 (s : N.State) (i : N.Inputs) :
  R.v43221 (state s) (inputs i) = Zmod.unsigned (N.v43221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43221 s i)) at 1.
  unfold R.v43221, N.v43221.
  rewrite ?node_10677.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43222 (s : N.State) (i : N.Inputs) :
  R.v43222 (state s) (inputs i) = Zmod.unsigned (N.v43222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43222 s i)) at 1.
  unfold R.v43222, N.v43222.
  unfold R.v6, N.v6.
  rewrite ?node_10845.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43223 (s : N.State) (i : N.Inputs) :
  R.v43223 (state s) (inputs i) = Zmod.unsigned (N.v43223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43223 s i)) at 1.
  unfold R.v43223, N.v43223.
  rewrite ?node_43221.
  rewrite ?node_43222.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43224 (s : N.State) (i : N.Inputs) :
  R.v43224 (state s) (inputs i) = Zmod.unsigned (N.v43224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43224 s i)) at 1.
  unfold R.v43224, N.v43224.
  rewrite ?node_43220.
  rewrite ?node_43223.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43225 (s : N.State) (i : N.Inputs) :
  R.v43225 (state s) (inputs i) = Zmod.unsigned (N.v43225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43225 s i)) at 1.
  unfold R.v43225, N.v43225.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43226 (s : N.State) (i : N.Inputs) :
  R.v43226 (state s) (inputs i) = Zmod.unsigned (N.v43226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43226 s i)) at 1.
  unfold R.v43226, N.v43226.
  rewrite ?node_10684.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43227 (s : N.State) (i : N.Inputs) :
  R.v43227 (state s) (inputs i) = Zmod.unsigned (N.v43227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43227 s i)) at 1.
  unfold R.v43227, N.v43227.
  unfold R.v6, N.v6.
  rewrite ?node_10680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43228 (s : N.State) (i : N.Inputs) :
  R.v43228 (state s) (inputs i) = Zmod.unsigned (N.v43228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43228 s i)) at 1.
  unfold R.v43228, N.v43228.
  unfold R.v6, N.v6.
  rewrite ?node_10677.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43229 (s : N.State) (i : N.Inputs) :
  R.v43229 (state s) (inputs i) = Zmod.unsigned (N.v43229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43229 s i)) at 1.
  unfold R.v43229, N.v43229.
  rewrite ?node_43227.
  rewrite ?node_43228.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43230 (s : N.State) (i : N.Inputs) :
  R.v43230 (state s) (inputs i) = Zmod.unsigned (N.v43230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43230 s i)) at 1.
  unfold R.v43230, N.v43230.
  unfold R.v16484, N.v16484.
  rewrite ?node_43229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43231 (s : N.State) (i : N.Inputs) :
  R.v43231 (state s) (inputs i) = Zmod.unsigned (N.v43231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43231 s i)) at 1.
  unfold R.v43231, N.v43231.
  rewrite ?node_43226.
  rewrite ?node_43230.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43232 (s : N.State) (i : N.Inputs) :
  R.v43232 (state s) (inputs i) = Zmod.unsigned (N.v43232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43232 s i)) at 1.
  unfold R.v43232, N.v43232.
  unfold R.v6, N.v6.
  rewrite ?node_43231.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43233 (s : N.State) (i : N.Inputs) :
  R.v43233 (state s) (inputs i) = Zmod.unsigned (N.v43233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43233 s i)) at 1.
  unfold R.v43233, N.v43233.
  rewrite ?node_10685.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43234 (s : N.State) (i : N.Inputs) :
  R.v43234 (state s) (inputs i) = Zmod.unsigned (N.v43234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43234 s i)) at 1.
  unfold R.v43234, N.v43234.
  unfold R.v6, N.v6.
  rewrite ?node_10885.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43235 (s : N.State) (i : N.Inputs) :
  R.v43235 (state s) (inputs i) = Zmod.unsigned (N.v43235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43235 s i)) at 1.
  unfold R.v43235, N.v43235.
  rewrite ?node_43233.
  rewrite ?node_43234.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43236 (s : N.State) (i : N.Inputs) :
  R.v43236 (state s) (inputs i) = Zmod.unsigned (N.v43236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43236 s i)) at 1.
  unfold R.v43236, N.v43236.
  rewrite ?node_43232.
  rewrite ?node_43235.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43237 (s : N.State) (i : N.Inputs) :
  R.v43237 (state s) (inputs i) = Zmod.unsigned (N.v43237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43237 s i)) at 1.
  unfold R.v43237, N.v43237.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43238 (s : N.State) (i : N.Inputs) :
  R.v43238 (state s) (inputs i) = Zmod.unsigned (N.v43238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43238 s i)) at 1.
  unfold R.v43238, N.v43238.
  rewrite ?node_10704.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43239 (s : N.State) (i : N.Inputs) :
  R.v43239 (state s) (inputs i) = Zmod.unsigned (N.v43239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43239 s i)) at 1.
  unfold R.v43239, N.v43239.
  rewrite ?node_10700.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43240 (s : N.State) (i : N.Inputs) :
  R.v43240 (state s) (inputs i) = Zmod.unsigned (N.v43240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43240 s i)) at 1.
  unfold R.v43240, N.v43240.
  rewrite ?node_10696.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43241 (s : N.State) (i : N.Inputs) :
  R.v43241 (state s) (inputs i) = Zmod.unsigned (N.v43241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43241 s i)) at 1.
  unfold R.v43241, N.v43241.
  unfold R.v6, N.v6.
  rewrite ?node_10692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43242 (s : N.State) (i : N.Inputs) :
  R.v43242 (state s) (inputs i) = Zmod.unsigned (N.v43242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43242 s i)) at 1.
  unfold R.v43242, N.v43242.
  unfold R.v6, N.v6.
  rewrite ?node_10689.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43243 (s : N.State) (i : N.Inputs) :
  R.v43243 (state s) (inputs i) = Zmod.unsigned (N.v43243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43243 s i)) at 1.
  unfold R.v43243, N.v43243.
  rewrite ?node_43241.
  rewrite ?node_43242.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43244 (s : N.State) (i : N.Inputs) :
  R.v43244 (state s) (inputs i) = Zmod.unsigned (N.v43244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43244 s i)) at 1.
  unfold R.v43244, N.v43244.
  unfold R.v16484, N.v16484.
  rewrite ?node_43243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43245 (s : N.State) (i : N.Inputs) :
  R.v43245 (state s) (inputs i) = Zmod.unsigned (N.v43245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43245 s i)) at 1.
  unfold R.v43245, N.v43245.
  rewrite ?node_43238.
  rewrite ?node_43239.
  rewrite ?node_43240.
  rewrite ?node_43244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43246 (s : N.State) (i : N.Inputs) :
  R.v43246 (state s) (inputs i) = Zmod.unsigned (N.v43246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43246 s i)) at 1.
  unfold R.v43246, N.v43246.
  unfold R.v6, N.v6.
  rewrite ?node_43245.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43247 (s : N.State) (i : N.Inputs) :
  R.v43247 (state s) (inputs i) = Zmod.unsigned (N.v43247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43247 s i)) at 1.
  unfold R.v43247, N.v43247.
  rewrite ?node_10705.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43248 (s : N.State) (i : N.Inputs) :
  R.v43248 (state s) (inputs i) = Zmod.unsigned (N.v43248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43248 s i)) at 1.
  unfold R.v43248, N.v43248.
  unfold R.v6, N.v6.
  rewrite ?node_10865.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43249 (s : N.State) (i : N.Inputs) :
  R.v43249 (state s) (inputs i) = Zmod.unsigned (N.v43249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43249 s i)) at 1.
  unfold R.v43249, N.v43249.
  unfold R.v6, N.v6.
  rewrite ?node_10894.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43250 (s : N.State) (i : N.Inputs) :
  R.v43250 (state s) (inputs i) = Zmod.unsigned (N.v43250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43250 s i)) at 1.
  unfold R.v43250, N.v43250.
  rewrite ?node_43247.
  rewrite ?node_43248.
  rewrite ?node_43249.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43251 (s : N.State) (i : N.Inputs) :
  R.v43251 (state s) (inputs i) = Zmod.unsigned (N.v43251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43251 s i)) at 1.
  unfold R.v43251, N.v43251.
  rewrite ?node_43246.
  rewrite ?node_43250.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43252 (s : N.State) (i : N.Inputs) :
  R.v43252 (state s) (inputs i) = Zmod.unsigned (N.v43252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43252 s i)) at 1.
  unfold R.v43252, N.v43252.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43253 (s : N.State) (i : N.Inputs) :
  R.v43253 (state s) (inputs i) = Zmod.unsigned (N.v43253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43253 s i)) at 1.
  unfold R.v43253, N.v43253.
  rewrite ?node_10696.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43254 (s : N.State) (i : N.Inputs) :
  R.v43254 (state s) (inputs i) = Zmod.unsigned (N.v43254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43254 s i)) at 1.
  unfold R.v43254, N.v43254.
  unfold R.v6, N.v6.
  rewrite ?node_10692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43255 (s : N.State) (i : N.Inputs) :
  R.v43255 (state s) (inputs i) = Zmod.unsigned (N.v43255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43255 s i)) at 1.
  unfold R.v43255, N.v43255.
  unfold R.v6, N.v6.
  rewrite ?node_10689.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43256 (s : N.State) (i : N.Inputs) :
  R.v43256 (state s) (inputs i) = Zmod.unsigned (N.v43256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43256 s i)) at 1.
  unfold R.v43256, N.v43256.
  rewrite ?node_43254.
  rewrite ?node_43255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43257 (s : N.State) (i : N.Inputs) :
  R.v43257 (state s) (inputs i) = Zmod.unsigned (N.v43257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43257 s i)) at 1.
  unfold R.v43257, N.v43257.
  unfold R.v16484, N.v16484.
  rewrite ?node_43256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43258 (s : N.State) (i : N.Inputs) :
  R.v43258 (state s) (inputs i) = Zmod.unsigned (N.v43258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43258 s i)) at 1.
  unfold R.v43258, N.v43258.
  rewrite ?node_43253.
  rewrite ?node_43257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43259 (s : N.State) (i : N.Inputs) :
  R.v43259 (state s) (inputs i) = Zmod.unsigned (N.v43259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43259 s i)) at 1.
  unfold R.v43259, N.v43259.
  unfold R.v6, N.v6.
  rewrite ?node_43258.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43260 (s : N.State) (i : N.Inputs) :
  R.v43260 (state s) (inputs i) = Zmod.unsigned (N.v43260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43260 s i)) at 1.
  unfold R.v43260, N.v43260.
  rewrite ?node_10697.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43261 (s : N.State) (i : N.Inputs) :
  R.v43261 (state s) (inputs i) = Zmod.unsigned (N.v43261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43261 s i)) at 1.
  unfold R.v43261, N.v43261.
  unfold R.v6, N.v6.
  rewrite ?node_10865.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43262 (s : N.State) (i : N.Inputs) :
  R.v43262 (state s) (inputs i) = Zmod.unsigned (N.v43262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43262 s i)) at 1.
  unfold R.v43262, N.v43262.
  rewrite ?node_43260.
  rewrite ?node_43261.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43263 (s : N.State) (i : N.Inputs) :
  R.v43263 (state s) (inputs i) = Zmod.unsigned (N.v43263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43263 s i)) at 1.
  unfold R.v43263, N.v43263.
  rewrite ?node_43259.
  rewrite ?node_43262.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43264 (s : N.State) (i : N.Inputs) :
  R.v43264 (state s) (inputs i) = Zmod.unsigned (N.v43264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43264 s i)) at 1.
  unfold R.v43264, N.v43264.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43265 (s : N.State) (i : N.Inputs) :
  R.v43265 (state s) (inputs i) = Zmod.unsigned (N.v43265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43265 s i)) at 1.
  unfold R.v43265, N.v43265.
  rewrite ?node_10704.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43266 (s : N.State) (i : N.Inputs) :
  R.v43266 (state s) (inputs i) = Zmod.unsigned (N.v43266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43266 s i)) at 1.
  unfold R.v43266, N.v43266.
  unfold R.v6, N.v6.
  rewrite ?node_10700.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43267 (s : N.State) (i : N.Inputs) :
  R.v43267 (state s) (inputs i) = Zmod.unsigned (N.v43267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43267 s i)) at 1.
  unfold R.v43267, N.v43267.
  unfold R.v6, N.v6.
  rewrite ?node_10697.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43268 (s : N.State) (i : N.Inputs) :
  R.v43268 (state s) (inputs i) = Zmod.unsigned (N.v43268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43268 s i)) at 1.
  unfold R.v43268, N.v43268.
  rewrite ?node_43266.
  rewrite ?node_43267.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43269 (s : N.State) (i : N.Inputs) :
  R.v43269 (state s) (inputs i) = Zmod.unsigned (N.v43269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43269 s i)) at 1.
  unfold R.v43269, N.v43269.
  unfold R.v16484, N.v16484.
  rewrite ?node_43268.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43270 (s : N.State) (i : N.Inputs) :
  R.v43270 (state s) (inputs i) = Zmod.unsigned (N.v43270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43270 s i)) at 1.
  unfold R.v43270, N.v43270.
  rewrite ?node_43265.
  rewrite ?node_43269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43271 (s : N.State) (i : N.Inputs) :
  R.v43271 (state s) (inputs i) = Zmod.unsigned (N.v43271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43271 s i)) at 1.
  unfold R.v43271, N.v43271.
  unfold R.v6, N.v6.
  rewrite ?node_43270.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43272 (s : N.State) (i : N.Inputs) :
  R.v43272 (state s) (inputs i) = Zmod.unsigned (N.v43272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43272 s i)) at 1.
  unfold R.v43272, N.v43272.
  rewrite ?node_10705.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43273 (s : N.State) (i : N.Inputs) :
  R.v43273 (state s) (inputs i) = Zmod.unsigned (N.v43273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43273 s i)) at 1.
  unfold R.v43273, N.v43273.
  unfold R.v6, N.v6.
  rewrite ?node_10894.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43274 (s : N.State) (i : N.Inputs) :
  R.v43274 (state s) (inputs i) = Zmod.unsigned (N.v43274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43274 s i)) at 1.
  unfold R.v43274, N.v43274.
  rewrite ?node_43272.
  rewrite ?node_43273.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43275 (s : N.State) (i : N.Inputs) :
  R.v43275 (state s) (inputs i) = Zmod.unsigned (N.v43275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43275 s i)) at 1.
  unfold R.v43275, N.v43275.
  rewrite ?node_43271.
  rewrite ?node_43274.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43276 (s : N.State) (i : N.Inputs) :
  R.v43276 (state s) (inputs i) = Zmod.unsigned (N.v43276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43276 s i)) at 1.
  unfold R.v43276, N.v43276.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43277 (s : N.State) (i : N.Inputs) :
  R.v43277 (state s) (inputs i) = Zmod.unsigned (N.v43277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43277 s i)) at 1.
  unfold R.v43277, N.v43277.
  unfold R.v6, N.v6.
  rewrite ?node_10714.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43278 (s : N.State) (i : N.Inputs) :
  R.v43278 (state s) (inputs i) = Zmod.unsigned (N.v43278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43278 s i)) at 1.
  unfold R.v43278, N.v43278.
  unfold R.v6, N.v6.
  rewrite ?node_10713.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43279 (s : N.State) (i : N.Inputs) :
  R.v43279 (state s) (inputs i) = Zmod.unsigned (N.v43279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43279 s i)) at 1.
  unfold R.v43279, N.v43279.
  rewrite ?node_43277.
  rewrite ?node_43278.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43280 (s : N.State) (i : N.Inputs) :
  R.v43280 (state s) (inputs i) = Zmod.unsigned (N.v43280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43280 s i)) at 1.
  unfold R.v43280, N.v43280.
  unfold R.v16463, N.v16463.
  rewrite ?node_43279.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43281 (s : N.State) (i : N.Inputs) :
  R.v43281 (state s) (inputs i) = Zmod.unsigned (N.v43281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43281 s i)) at 1.
  unfold R.v43281, N.v43281.
  rewrite ?node_10715.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43282 (s : N.State) (i : N.Inputs) :
  R.v43282 (state s) (inputs i) = Zmod.unsigned (N.v43282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43282 s i)) at 1.
  unfold R.v43282, N.v43282.
  unfold R.v6, N.v6.
  rewrite ?node_10895.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43283 (s : N.State) (i : N.Inputs) :
  R.v43283 (state s) (inputs i) = Zmod.unsigned (N.v43283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43283 s i)) at 1.
  unfold R.v43283, N.v43283.
  rewrite ?node_43281.
  rewrite ?node_43282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43284 (s : N.State) (i : N.Inputs) :
  R.v43284 (state s) (inputs i) = Zmod.unsigned (N.v43284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43284 s i)) at 1.
  unfold R.v43284, N.v43284.
  rewrite ?node_43280.
  rewrite ?node_43283.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43285 (s : N.State) (i : N.Inputs) :
  R.v43285 (state s) (inputs i) = Zmod.unsigned (N.v43285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43285 s i)) at 1.
  unfold R.v43285, N.v43285.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43286 (s : N.State) (i : N.Inputs) :
  R.v43286 (state s) (inputs i) = Zmod.unsigned (N.v43286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43286 s i)) at 1.
  unfold R.v43286, N.v43286.
  rewrite ?node_10793.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43287 (s : N.State) (i : N.Inputs) :
  R.v43287 (state s) (inputs i) = Zmod.unsigned (N.v43287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43287 s i)) at 1.
  unfold R.v43287, N.v43287.
  rewrite ?node_10789.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43288 (s : N.State) (i : N.Inputs) :
  R.v43288 (state s) (inputs i) = Zmod.unsigned (N.v43288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43288 s i)) at 1.
  unfold R.v43288, N.v43288.
  rewrite ?node_10781.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43289 (s : N.State) (i : N.Inputs) :
  R.v43289 (state s) (inputs i) = Zmod.unsigned (N.v43289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43289 s i)) at 1.
  unfold R.v43289, N.v43289.
  unfold R.v6, N.v6.
  rewrite ?node_10773.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43290 (s : N.State) (i : N.Inputs) :
  R.v43290 (state s) (inputs i) = Zmod.unsigned (N.v43290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43290 s i)) at 1.
  unfold R.v43290, N.v43290.
  unfold R.v6, N.v6.
  rewrite ?node_10766.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43291 (s : N.State) (i : N.Inputs) :
  R.v43291 (state s) (inputs i) = Zmod.unsigned (N.v43291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43291 s i)) at 1.
  unfold R.v43291, N.v43291.
  rewrite ?node_43289.
  rewrite ?node_43290.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43292 (s : N.State) (i : N.Inputs) :
  R.v43292 (state s) (inputs i) = Zmod.unsigned (N.v43292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43292 s i)) at 1.
  unfold R.v43292, N.v43292.
  unfold R.v16484, N.v16484.
  rewrite ?node_43291.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43293 (s : N.State) (i : N.Inputs) :
  R.v43293 (state s) (inputs i) = Zmod.unsigned (N.v43293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43293 s i)) at 1.
  unfold R.v43293, N.v43293.
  rewrite ?node_43286.
  rewrite ?node_43287.
  rewrite ?node_43288.
  rewrite ?node_43292.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43294 (s : N.State) (i : N.Inputs) :
  R.v43294 (state s) (inputs i) = Zmod.unsigned (N.v43294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43294 s i)) at 1.
  unfold R.v43294, N.v43294.
  unfold R.v6, N.v6.
  rewrite ?node_43293.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43295 (s : N.State) (i : N.Inputs) :
  R.v43295 (state s) (inputs i) = Zmod.unsigned (N.v43295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43295 s i)) at 1.
  unfold R.v43295, N.v43295.
  rewrite ?node_10794.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43296 (s : N.State) (i : N.Inputs) :
  R.v43296 (state s) (inputs i) = Zmod.unsigned (N.v43296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43296 s i)) at 1.
  unfold R.v43296, N.v43296.
  unfold R.v6, N.v6.
  rewrite ?node_10954.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43297 (s : N.State) (i : N.Inputs) :
  R.v43297 (state s) (inputs i) = Zmod.unsigned (N.v43297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43297 s i)) at 1.
  unfold R.v43297, N.v43297.
  unfold R.v6, N.v6.
  rewrite ?node_11038.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43298 (s : N.State) (i : N.Inputs) :
  R.v43298 (state s) (inputs i) = Zmod.unsigned (N.v43298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43298 s i)) at 1.
  unfold R.v43298, N.v43298.
  rewrite ?node_43295.
  rewrite ?node_43296.
  rewrite ?node_43297.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43299 (s : N.State) (i : N.Inputs) :
  R.v43299 (state s) (inputs i) = Zmod.unsigned (N.v43299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43299 s i)) at 1.
  unfold R.v43299, N.v43299.
  rewrite ?node_43294.
  rewrite ?node_43298.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43300 (s : N.State) (i : N.Inputs) :
  R.v43300 (state s) (inputs i) = Zmod.unsigned (N.v43300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43300 s i)) at 1.
  unfold R.v43300, N.v43300.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43301 (s : N.State) (i : N.Inputs) :
  R.v43301 (state s) (inputs i) = Zmod.unsigned (N.v43301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43301 s i)) at 1.
  unfold R.v43301, N.v43301.
  rewrite ?node_10781.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43302 (s : N.State) (i : N.Inputs) :
  R.v43302 (state s) (inputs i) = Zmod.unsigned (N.v43302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43302 s i)) at 1.
  unfold R.v43302, N.v43302.
  unfold R.v6, N.v6.
  rewrite ?node_10773.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43303 (s : N.State) (i : N.Inputs) :
  R.v43303 (state s) (inputs i) = Zmod.unsigned (N.v43303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43303 s i)) at 1.
  unfold R.v43303, N.v43303.
  unfold R.v6, N.v6.
  rewrite ?node_10766.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43304 (s : N.State) (i : N.Inputs) :
  R.v43304 (state s) (inputs i) = Zmod.unsigned (N.v43304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43304 s i)) at 1.
  unfold R.v43304, N.v43304.
  rewrite ?node_43302.
  rewrite ?node_43303.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43305 (s : N.State) (i : N.Inputs) :
  R.v43305 (state s) (inputs i) = Zmod.unsigned (N.v43305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43305 s i)) at 1.
  unfold R.v43305, N.v43305.
  unfold R.v16484, N.v16484.
  rewrite ?node_43304.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43306 (s : N.State) (i : N.Inputs) :
  R.v43306 (state s) (inputs i) = Zmod.unsigned (N.v43306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43306 s i)) at 1.
  unfold R.v43306, N.v43306.
  rewrite ?node_43301.
  rewrite ?node_43305.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43307 (s : N.State) (i : N.Inputs) :
  R.v43307 (state s) (inputs i) = Zmod.unsigned (N.v43307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43307 s i)) at 1.
  unfold R.v43307, N.v43307.
  unfold R.v6, N.v6.
  rewrite ?node_43306.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43308 (s : N.State) (i : N.Inputs) :
  R.v43308 (state s) (inputs i) = Zmod.unsigned (N.v43308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43308 s i)) at 1.
  unfold R.v43308, N.v43308.
  rewrite ?node_10782.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43309 (s : N.State) (i : N.Inputs) :
  R.v43309 (state s) (inputs i) = Zmod.unsigned (N.v43309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43309 s i)) at 1.
  unfold R.v43309, N.v43309.
  unfold R.v6, N.v6.
  rewrite ?node_10954.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43310 (s : N.State) (i : N.Inputs) :
  R.v43310 (state s) (inputs i) = Zmod.unsigned (N.v43310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43310 s i)) at 1.
  unfold R.v43310, N.v43310.
  rewrite ?node_43308.
  rewrite ?node_43309.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43311 (s : N.State) (i : N.Inputs) :
  R.v43311 (state s) (inputs i) = Zmod.unsigned (N.v43311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43311 s i)) at 1.
  unfold R.v43311, N.v43311.
  rewrite ?node_43307.
  rewrite ?node_43310.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43312 (s : N.State) (i : N.Inputs) :
  R.v43312 (state s) (inputs i) = Zmod.unsigned (N.v43312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43312 s i)) at 1.
  unfold R.v43312, N.v43312.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43313 (s : N.State) (i : N.Inputs) :
  R.v43313 (state s) (inputs i) = Zmod.unsigned (N.v43313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43313 s i)) at 1.
  unfold R.v43313, N.v43313.
  rewrite ?node_10793.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43314 (s : N.State) (i : N.Inputs) :
  R.v43314 (state s) (inputs i) = Zmod.unsigned (N.v43314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43314 s i)) at 1.
  unfold R.v43314, N.v43314.
  unfold R.v6, N.v6.
  rewrite ?node_10789.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43315 (s : N.State) (i : N.Inputs) :
  R.v43315 (state s) (inputs i) = Zmod.unsigned (N.v43315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43315 s i)) at 1.
  unfold R.v43315, N.v43315.
  unfold R.v6, N.v6.
  rewrite ?node_10782.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43316 (s : N.State) (i : N.Inputs) :
  R.v43316 (state s) (inputs i) = Zmod.unsigned (N.v43316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43316 s i)) at 1.
  unfold R.v43316, N.v43316.
  rewrite ?node_43314.
  rewrite ?node_43315.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43317 (s : N.State) (i : N.Inputs) :
  R.v43317 (state s) (inputs i) = Zmod.unsigned (N.v43317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43317 s i)) at 1.
  unfold R.v43317, N.v43317.
  unfold R.v16484, N.v16484.
  rewrite ?node_43316.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43318 (s : N.State) (i : N.Inputs) :
  R.v43318 (state s) (inputs i) = Zmod.unsigned (N.v43318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43318 s i)) at 1.
  unfold R.v43318, N.v43318.
  rewrite ?node_43313.
  rewrite ?node_43317.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43319 (s : N.State) (i : N.Inputs) :
  R.v43319 (state s) (inputs i) = Zmod.unsigned (N.v43319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43319 s i)) at 1.
  unfold R.v43319, N.v43319.
  unfold R.v6, N.v6.
  rewrite ?node_43318.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43320 (s : N.State) (i : N.Inputs) :
  R.v43320 (state s) (inputs i) = Zmod.unsigned (N.v43320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43320 s i)) at 1.
  unfold R.v43320, N.v43320.
  rewrite ?node_10794.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43321 (s : N.State) (i : N.Inputs) :
  R.v43321 (state s) (inputs i) = Zmod.unsigned (N.v43321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43321 s i)) at 1.
  unfold R.v43321, N.v43321.
  unfold R.v6, N.v6.
  rewrite ?node_11038.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43322 (s : N.State) (i : N.Inputs) :
  R.v43322 (state s) (inputs i) = Zmod.unsigned (N.v43322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43322 s i)) at 1.
  unfold R.v43322, N.v43322.
  rewrite ?node_43320.
  rewrite ?node_43321.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43323 (s : N.State) (i : N.Inputs) :
  R.v43323 (state s) (inputs i) = Zmod.unsigned (N.v43323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43323 s i)) at 1.
  unfold R.v43323, N.v43323.
  rewrite ?node_43319.
  rewrite ?node_43322.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43324 (s : N.State) (i : N.Inputs) :
  R.v43324 (state s) (inputs i) = Zmod.unsigned (N.v43324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43324 s i)) at 1.
  unfold R.v43324, N.v43324.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43325 (s : N.State) (i : N.Inputs) :
  R.v43325 (state s) (inputs i) = Zmod.unsigned (N.v43325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43325 s i)) at 1.
  unfold R.v43325, N.v43325.
  rewrite ?node_10828.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43326 (s : N.State) (i : N.Inputs) :
  R.v43326 (state s) (inputs i) = Zmod.unsigned (N.v43326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43326 s i)) at 1.
  unfold R.v43326, N.v43326.
  rewrite ?node_10824.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43327 (s : N.State) (i : N.Inputs) :
  R.v43327 (state s) (inputs i) = Zmod.unsigned (N.v43327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43327 s i)) at 1.
  unfold R.v43327, N.v43327.
  rewrite ?node_10816.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43328 (s : N.State) (i : N.Inputs) :
  R.v43328 (state s) (inputs i) = Zmod.unsigned (N.v43328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43328 s i)) at 1.
  unfold R.v43328, N.v43328.
  unfold R.v6, N.v6.
  rewrite ?node_10808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43329 (s : N.State) (i : N.Inputs) :
  R.v43329 (state s) (inputs i) = Zmod.unsigned (N.v43329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43329 s i)) at 1.
  unfold R.v43329, N.v43329.
  unfold R.v6, N.v6.
  rewrite ?node_10801.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43330 (s : N.State) (i : N.Inputs) :
  R.v43330 (state s) (inputs i) = Zmod.unsigned (N.v43330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43330 s i)) at 1.
  unfold R.v43330, N.v43330.
  rewrite ?node_43328.
  rewrite ?node_43329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43331 (s : N.State) (i : N.Inputs) :
  R.v43331 (state s) (inputs i) = Zmod.unsigned (N.v43331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43331 s i)) at 1.
  unfold R.v43331, N.v43331.
  unfold R.v16484, N.v16484.
  rewrite ?node_43330.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43332 (s : N.State) (i : N.Inputs) :
  R.v43332 (state s) (inputs i) = Zmod.unsigned (N.v43332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43332 s i)) at 1.
  unfold R.v43332, N.v43332.
  rewrite ?node_43325.
  rewrite ?node_43326.
  rewrite ?node_43327.
  rewrite ?node_43331.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43333 (s : N.State) (i : N.Inputs) :
  R.v43333 (state s) (inputs i) = Zmod.unsigned (N.v43333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43333 s i)) at 1.
  unfold R.v43333, N.v43333.
  unfold R.v6, N.v6.
  rewrite ?node_43332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43334 (s : N.State) (i : N.Inputs) :
  R.v43334 (state s) (inputs i) = Zmod.unsigned (N.v43334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43334 s i)) at 1.
  unfold R.v43334, N.v43334.
  rewrite ?node_10829.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43335 (s : N.State) (i : N.Inputs) :
  R.v43335 (state s) (inputs i) = Zmod.unsigned (N.v43335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43335 s i)) at 1.
  unfold R.v43335, N.v43335.
  unfold R.v6, N.v6.
  rewrite ?node_10989.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43336 (s : N.State) (i : N.Inputs) :
  R.v43336 (state s) (inputs i) = Zmod.unsigned (N.v43336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43336 s i)) at 1.
  unfold R.v43336, N.v43336.
  unfold R.v6, N.v6.
  rewrite ?node_11042.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43337 (s : N.State) (i : N.Inputs) :
  R.v43337 (state s) (inputs i) = Zmod.unsigned (N.v43337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43337 s i)) at 1.
  unfold R.v43337, N.v43337.
  rewrite ?node_43334.
  rewrite ?node_43335.
  rewrite ?node_43336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43338 (s : N.State) (i : N.Inputs) :
  R.v43338 (state s) (inputs i) = Zmod.unsigned (N.v43338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43338 s i)) at 1.
  unfold R.v43338, N.v43338.
  rewrite ?node_43333.
  rewrite ?node_43337.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43339 (s : N.State) (i : N.Inputs) :
  R.v43339 (state s) (inputs i) = Zmod.unsigned (N.v43339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43339 s i)) at 1.
  unfold R.v43339, N.v43339.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43340 (s : N.State) (i : N.Inputs) :
  R.v43340 (state s) (inputs i) = Zmod.unsigned (N.v43340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43340 s i)) at 1.
  unfold R.v43340, N.v43340.
  rewrite ?node_10816.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43341 (s : N.State) (i : N.Inputs) :
  R.v43341 (state s) (inputs i) = Zmod.unsigned (N.v43341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43341 s i)) at 1.
  unfold R.v43341, N.v43341.
  unfold R.v6, N.v6.
  rewrite ?node_10808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43342 (s : N.State) (i : N.Inputs) :
  R.v43342 (state s) (inputs i) = Zmod.unsigned (N.v43342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43342 s i)) at 1.
  unfold R.v43342, N.v43342.
  unfold R.v6, N.v6.
  rewrite ?node_10801.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43343 (s : N.State) (i : N.Inputs) :
  R.v43343 (state s) (inputs i) = Zmod.unsigned (N.v43343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43343 s i)) at 1.
  unfold R.v43343, N.v43343.
  rewrite ?node_43341.
  rewrite ?node_43342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43344 (s : N.State) (i : N.Inputs) :
  R.v43344 (state s) (inputs i) = Zmod.unsigned (N.v43344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43344 s i)) at 1.
  unfold R.v43344, N.v43344.
  unfold R.v16484, N.v16484.
  rewrite ?node_43343.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43345 (s : N.State) (i : N.Inputs) :
  R.v43345 (state s) (inputs i) = Zmod.unsigned (N.v43345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43345 s i)) at 1.
  unfold R.v43345, N.v43345.
  rewrite ?node_43340.
  rewrite ?node_43344.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43346 (s : N.State) (i : N.Inputs) :
  R.v43346 (state s) (inputs i) = Zmod.unsigned (N.v43346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43346 s i)) at 1.
  unfold R.v43346, N.v43346.
  unfold R.v6, N.v6.
  rewrite ?node_43345.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43347 (s : N.State) (i : N.Inputs) :
  R.v43347 (state s) (inputs i) = Zmod.unsigned (N.v43347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43347 s i)) at 1.
  unfold R.v43347, N.v43347.
  rewrite ?node_10817.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43348 (s : N.State) (i : N.Inputs) :
  R.v43348 (state s) (inputs i) = Zmod.unsigned (N.v43348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43348 s i)) at 1.
  unfold R.v43348, N.v43348.
  unfold R.v6, N.v6.
  rewrite ?node_10989.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43349 (s : N.State) (i : N.Inputs) :
  R.v43349 (state s) (inputs i) = Zmod.unsigned (N.v43349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43349 s i)) at 1.
  unfold R.v43349, N.v43349.
  rewrite ?node_43347.
  rewrite ?node_43348.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43350 (s : N.State) (i : N.Inputs) :
  R.v43350 (state s) (inputs i) = Zmod.unsigned (N.v43350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43350 s i)) at 1.
  unfold R.v43350, N.v43350.
  rewrite ?node_43346.
  rewrite ?node_43349.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43351 (s : N.State) (i : N.Inputs) :
  R.v43351 (state s) (inputs i) = Zmod.unsigned (N.v43351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43351 s i)) at 1.
  unfold R.v43351, N.v43351.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43352 (s : N.State) (i : N.Inputs) :
  R.v43352 (state s) (inputs i) = Zmod.unsigned (N.v43352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43352 s i)) at 1.
  unfold R.v43352, N.v43352.
  rewrite ?node_10828.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43353 (s : N.State) (i : N.Inputs) :
  R.v43353 (state s) (inputs i) = Zmod.unsigned (N.v43353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43353 s i)) at 1.
  unfold R.v43353, N.v43353.
  unfold R.v6, N.v6.
  rewrite ?node_10824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43354 (s : N.State) (i : N.Inputs) :
  R.v43354 (state s) (inputs i) = Zmod.unsigned (N.v43354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43354 s i)) at 1.
  unfold R.v43354, N.v43354.
  unfold R.v6, N.v6.
  rewrite ?node_10817.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43355 (s : N.State) (i : N.Inputs) :
  R.v43355 (state s) (inputs i) = Zmod.unsigned (N.v43355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43355 s i)) at 1.
  unfold R.v43355, N.v43355.
  rewrite ?node_43353.
  rewrite ?node_43354.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43356 (s : N.State) (i : N.Inputs) :
  R.v43356 (state s) (inputs i) = Zmod.unsigned (N.v43356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43356 s i)) at 1.
  unfold R.v43356, N.v43356.
  unfold R.v16484, N.v16484.
  rewrite ?node_43355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43357 (s : N.State) (i : N.Inputs) :
  R.v43357 (state s) (inputs i) = Zmod.unsigned (N.v43357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43357 s i)) at 1.
  unfold R.v43357, N.v43357.
  rewrite ?node_43352.
  rewrite ?node_43356.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43358 (s : N.State) (i : N.Inputs) :
  R.v43358 (state s) (inputs i) = Zmod.unsigned (N.v43358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43358 s i)) at 1.
  unfold R.v43358, N.v43358.
  unfold R.v6, N.v6.
  rewrite ?node_43357.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43359 (s : N.State) (i : N.Inputs) :
  R.v43359 (state s) (inputs i) = Zmod.unsigned (N.v43359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43359 s i)) at 1.
  unfold R.v43359, N.v43359.
  rewrite ?node_10829.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43360 (s : N.State) (i : N.Inputs) :
  R.v43360 (state s) (inputs i) = Zmod.unsigned (N.v43360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43360 s i)) at 1.
  unfold R.v43360, N.v43360.
  unfold R.v6, N.v6.
  rewrite ?node_11042.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43361 (s : N.State) (i : N.Inputs) :
  R.v43361 (state s) (inputs i) = Zmod.unsigned (N.v43361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43361 s i)) at 1.
  unfold R.v43361, N.v43361.
  rewrite ?node_43359.
  rewrite ?node_43360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43362 (s : N.State) (i : N.Inputs) :
  R.v43362 (state s) (inputs i) = Zmod.unsigned (N.v43362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43362 s i)) at 1.
  unfold R.v43362, N.v43362.
  rewrite ?node_43358.
  rewrite ?node_43361.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43363 (s : N.State) (i : N.Inputs) :
  R.v43363 (state s) (inputs i) = Zmod.unsigned (N.v43363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43363 s i)) at 1.
  unfold R.v43363, N.v43363.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43364 (s : N.State) (i : N.Inputs) :
  R.v43364 (state s) (inputs i) = Zmod.unsigned (N.v43364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43364 s i)) at 1.
  unfold R.v43364, N.v43364.
  rewrite ?node_10845.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43365 (s : N.State) (i : N.Inputs) :
  R.v43365 (state s) (inputs i) = Zmod.unsigned (N.v43365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43365 s i)) at 1.
  unfold R.v43365, N.v43365.
  rewrite ?node_10841.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43366 (s : N.State) (i : N.Inputs) :
  R.v43366 (state s) (inputs i) = Zmod.unsigned (N.v43366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43366 s i)) at 1.
  unfold R.v43366, N.v43366.
  rewrite ?node_10837.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43367 (s : N.State) (i : N.Inputs) :
  R.v43367 (state s) (inputs i) = Zmod.unsigned (N.v43367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43367 s i)) at 1.
  unfold R.v43367, N.v43367.
  unfold R.v6, N.v6.
  rewrite ?node_10833.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43368 (s : N.State) (i : N.Inputs) :
  R.v43368 (state s) (inputs i) = Zmod.unsigned (N.v43368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43368 s i)) at 1.
  unfold R.v43368, N.v43368.
  unfold R.v6, N.v6.
  rewrite !state_r1253_nr_5F1253.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1253_nr_5F1253 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43369 (s : N.State) (i : N.Inputs) :
  R.v43369 (state s) (inputs i) = Zmod.unsigned (N.v43369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43369 s i)) at 1.
  unfold R.v43369, N.v43369.
  rewrite ?node_43367.
  rewrite ?node_43368.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43370 (s : N.State) (i : N.Inputs) :
  R.v43370 (state s) (inputs i) = Zmod.unsigned (N.v43370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43370 s i)) at 1.
  unfold R.v43370, N.v43370.
  unfold R.v16484, N.v16484.
  rewrite ?node_43369.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43371 (s : N.State) (i : N.Inputs) :
  R.v43371 (state s) (inputs i) = Zmod.unsigned (N.v43371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43371 s i)) at 1.
  unfold R.v43371, N.v43371.
  rewrite ?node_43364.
  rewrite ?node_43365.
  rewrite ?node_43366.
  rewrite ?node_43370.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43372 (s : N.State) (i : N.Inputs) :
  R.v43372 (state s) (inputs i) = Zmod.unsigned (N.v43372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43372 s i)) at 1.
  unfold R.v43372, N.v43372.
  unfold R.v6, N.v6.
  rewrite ?node_43371.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43373 (s : N.State) (i : N.Inputs) :
  R.v43373 (state s) (inputs i) = Zmod.unsigned (N.v43373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43373 s i)) at 1.
  unfold R.v43373, N.v43373.
  rewrite ?node_10846.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43374 (s : N.State) (i : N.Inputs) :
  R.v43374 (state s) (inputs i) = Zmod.unsigned (N.v43374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43374 s i)) at 1.
  unfold R.v43374, N.v43374.
  unfold R.v6, N.v6.
  rewrite ?node_11006.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43375 (s : N.State) (i : N.Inputs) :
  R.v43375 (state s) (inputs i) = Zmod.unsigned (N.v43375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43375 s i)) at 1.
  unfold R.v43375, N.v43375.
  unfold R.v6, N.v6.
  rewrite ?node_11046.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43376 (s : N.State) (i : N.Inputs) :
  R.v43376 (state s) (inputs i) = Zmod.unsigned (N.v43376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43376 s i)) at 1.
  unfold R.v43376, N.v43376.
  rewrite ?node_43373.
  rewrite ?node_43374.
  rewrite ?node_43375.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43377 (s : N.State) (i : N.Inputs) :
  R.v43377 (state s) (inputs i) = Zmod.unsigned (N.v43377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43377 s i)) at 1.
  unfold R.v43377, N.v43377.
  rewrite ?node_43372.
  rewrite ?node_43376.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43378 (s : N.State) (i : N.Inputs) :
  R.v43378 (state s) (inputs i) = Zmod.unsigned (N.v43378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43378 s i)) at 1.
  unfold R.v43378, N.v43378.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43379 (s : N.State) (i : N.Inputs) :
  R.v43379 (state s) (inputs i) = Zmod.unsigned (N.v43379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43379 s i)) at 1.
  unfold R.v43379, N.v43379.
  rewrite ?node_10837.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43380 (s : N.State) (i : N.Inputs) :
  R.v43380 (state s) (inputs i) = Zmod.unsigned (N.v43380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43380 s i)) at 1.
  unfold R.v43380, N.v43380.
  unfold R.v6, N.v6.
  rewrite ?node_10833.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43381 (s : N.State) (i : N.Inputs) :
  R.v43381 (state s) (inputs i) = Zmod.unsigned (N.v43381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43381 s i)) at 1.
  unfold R.v43381, N.v43381.
  unfold R.v6, N.v6.
  rewrite !state_r1253_nr_5F1253.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1253_nr_5F1253 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43382 (s : N.State) (i : N.Inputs) :
  R.v43382 (state s) (inputs i) = Zmod.unsigned (N.v43382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43382 s i)) at 1.
  unfold R.v43382, N.v43382.
  rewrite ?node_43380.
  rewrite ?node_43381.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43383 (s : N.State) (i : N.Inputs) :
  R.v43383 (state s) (inputs i) = Zmod.unsigned (N.v43383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43383 s i)) at 1.
  unfold R.v43383, N.v43383.
  unfold R.v16484, N.v16484.
  rewrite ?node_43382.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43384 (s : N.State) (i : N.Inputs) :
  R.v43384 (state s) (inputs i) = Zmod.unsigned (N.v43384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43384 s i)) at 1.
  unfold R.v43384, N.v43384.
  rewrite ?node_43379.
  rewrite ?node_43383.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43385 (s : N.State) (i : N.Inputs) :
  R.v43385 (state s) (inputs i) = Zmod.unsigned (N.v43385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43385 s i)) at 1.
  unfold R.v43385, N.v43385.
  unfold R.v6, N.v6.
  rewrite ?node_43384.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43386 (s : N.State) (i : N.Inputs) :
  R.v43386 (state s) (inputs i) = Zmod.unsigned (N.v43386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43386 s i)) at 1.
  unfold R.v43386, N.v43386.
  rewrite ?node_10838.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43387 (s : N.State) (i : N.Inputs) :
  R.v43387 (state s) (inputs i) = Zmod.unsigned (N.v43387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43387 s i)) at 1.
  unfold R.v43387, N.v43387.
  unfold R.v6, N.v6.
  rewrite ?node_11006.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43388 (s : N.State) (i : N.Inputs) :
  R.v43388 (state s) (inputs i) = Zmod.unsigned (N.v43388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43388 s i)) at 1.
  unfold R.v43388, N.v43388.
  rewrite ?node_43386.
  rewrite ?node_43387.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43389 (s : N.State) (i : N.Inputs) :
  R.v43389 (state s) (inputs i) = Zmod.unsigned (N.v43389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43389 s i)) at 1.
  unfold R.v43389, N.v43389.
  rewrite ?node_43385.
  rewrite ?node_43388.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43390 (s : N.State) (i : N.Inputs) :
  R.v43390 (state s) (inputs i) = Zmod.unsigned (N.v43390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43390 s i)) at 1.
  unfold R.v43390, N.v43390.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43391 (s : N.State) (i : N.Inputs) :
  R.v43391 (state s) (inputs i) = Zmod.unsigned (N.v43391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43391 s i)) at 1.
  unfold R.v43391, N.v43391.
  rewrite ?node_10845.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43392 (s : N.State) (i : N.Inputs) :
  R.v43392 (state s) (inputs i) = Zmod.unsigned (N.v43392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43392 s i)) at 1.
  unfold R.v43392, N.v43392.
  unfold R.v6, N.v6.
  rewrite ?node_10841.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43393 (s : N.State) (i : N.Inputs) :
  R.v43393 (state s) (inputs i) = Zmod.unsigned (N.v43393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43393 s i)) at 1.
  unfold R.v43393, N.v43393.
  unfold R.v6, N.v6.
  rewrite ?node_10838.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43394 (s : N.State) (i : N.Inputs) :
  R.v43394 (state s) (inputs i) = Zmod.unsigned (N.v43394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43394 s i)) at 1.
  unfold R.v43394, N.v43394.
  rewrite ?node_43392.
  rewrite ?node_43393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43395 (s : N.State) (i : N.Inputs) :
  R.v43395 (state s) (inputs i) = Zmod.unsigned (N.v43395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43395 s i)) at 1.
  unfold R.v43395, N.v43395.
  unfold R.v16484, N.v16484.
  rewrite ?node_43394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43396 (s : N.State) (i : N.Inputs) :
  R.v43396 (state s) (inputs i) = Zmod.unsigned (N.v43396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43396 s i)) at 1.
  unfold R.v43396, N.v43396.
  rewrite ?node_43391.
  rewrite ?node_43395.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43397 (s : N.State) (i : N.Inputs) :
  R.v43397 (state s) (inputs i) = Zmod.unsigned (N.v43397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43397 s i)) at 1.
  unfold R.v43397, N.v43397.
  unfold R.v6, N.v6.
  rewrite ?node_43396.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43398 (s : N.State) (i : N.Inputs) :
  R.v43398 (state s) (inputs i) = Zmod.unsigned (N.v43398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43398 s i)) at 1.
  unfold R.v43398, N.v43398.
  rewrite ?node_10846.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43399 (s : N.State) (i : N.Inputs) :
  R.v43399 (state s) (inputs i) = Zmod.unsigned (N.v43399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43399 s i)) at 1.
  unfold R.v43399, N.v43399.
  unfold R.v6, N.v6.
  rewrite ?node_11046.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43400 (s : N.State) (i : N.Inputs) :
  R.v43400 (state s) (inputs i) = Zmod.unsigned (N.v43400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43400 s i)) at 1.
  unfold R.v43400, N.v43400.
  rewrite ?node_43398.
  rewrite ?node_43399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43401 (s : N.State) (i : N.Inputs) :
  R.v43401 (state s) (inputs i) = Zmod.unsigned (N.v43401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43401 s i)) at 1.
  unfold R.v43401, N.v43401.
  rewrite ?node_43397.
  rewrite ?node_43400.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43402 (s : N.State) (i : N.Inputs) :
  R.v43402 (state s) (inputs i) = Zmod.unsigned (N.v43402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43402 s i)) at 1.
  unfold R.v43402, N.v43402.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43403 (s : N.State) (i : N.Inputs) :
  R.v43403 (state s) (inputs i) = Zmod.unsigned (N.v43403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43403 s i)) at 1.
  unfold R.v43403, N.v43403.
  rewrite ?node_10865.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43404 (s : N.State) (i : N.Inputs) :
  R.v43404 (state s) (inputs i) = Zmod.unsigned (N.v43404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43404 s i)) at 1.
  unfold R.v43404, N.v43404.
  rewrite ?node_10861.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43405 (s : N.State) (i : N.Inputs) :
  R.v43405 (state s) (inputs i) = Zmod.unsigned (N.v43405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43405 s i)) at 1.
  unfold R.v43405, N.v43405.
  rewrite ?node_10857.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43406 (s : N.State) (i : N.Inputs) :
  R.v43406 (state s) (inputs i) = Zmod.unsigned (N.v43406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43406 s i)) at 1.
  unfold R.v43406, N.v43406.
  unfold R.v6, N.v6.
  rewrite ?node_10853.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43407 (s : N.State) (i : N.Inputs) :
  R.v43407 (state s) (inputs i) = Zmod.unsigned (N.v43407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43407 s i)) at 1.
  unfold R.v43407, N.v43407.
  unfold R.v6, N.v6.
  rewrite ?node_10850.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43408 (s : N.State) (i : N.Inputs) :
  R.v43408 (state s) (inputs i) = Zmod.unsigned (N.v43408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43408 s i)) at 1.
  unfold R.v43408, N.v43408.
  rewrite ?node_43406.
  rewrite ?node_43407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43409 (s : N.State) (i : N.Inputs) :
  R.v43409 (state s) (inputs i) = Zmod.unsigned (N.v43409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43409 s i)) at 1.
  unfold R.v43409, N.v43409.
  unfold R.v16484, N.v16484.
  rewrite ?node_43408.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43410 (s : N.State) (i : N.Inputs) :
  R.v43410 (state s) (inputs i) = Zmod.unsigned (N.v43410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43410 s i)) at 1.
  unfold R.v43410, N.v43410.
  rewrite ?node_43403.
  rewrite ?node_43404.
  rewrite ?node_43405.
  rewrite ?node_43409.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43411 (s : N.State) (i : N.Inputs) :
  R.v43411 (state s) (inputs i) = Zmod.unsigned (N.v43411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43411 s i)) at 1.
  unfold R.v43411, N.v43411.
  unfold R.v6, N.v6.
  rewrite ?node_43410.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43412 (s : N.State) (i : N.Inputs) :
  R.v43412 (state s) (inputs i) = Zmod.unsigned (N.v43412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43412 s i)) at 1.
  unfold R.v43412, N.v43412.
  rewrite ?node_10866.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43413 (s : N.State) (i : N.Inputs) :
  R.v43413 (state s) (inputs i) = Zmod.unsigned (N.v43413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43413 s i)) at 1.
  unfold R.v43413, N.v43413.
  unfold R.v6, N.v6.
  rewrite ?node_11026.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43414 (s : N.State) (i : N.Inputs) :
  R.v43414 (state s) (inputs i) = Zmod.unsigned (N.v43414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43414 s i)) at 1.
  unfold R.v43414, N.v43414.
  unfold R.v6, N.v6.
  rewrite ?node_11055.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43415 (s : N.State) (i : N.Inputs) :
  R.v43415 (state s) (inputs i) = Zmod.unsigned (N.v43415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43415 s i)) at 1.
  unfold R.v43415, N.v43415.
  rewrite ?node_43412.
  rewrite ?node_43413.
  rewrite ?node_43414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43416 (s : N.State) (i : N.Inputs) :
  R.v43416 (state s) (inputs i) = Zmod.unsigned (N.v43416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43416 s i)) at 1.
  unfold R.v43416, N.v43416.
  rewrite ?node_43411.
  rewrite ?node_43415.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43417 (s : N.State) (i : N.Inputs) :
  R.v43417 (state s) (inputs i) = Zmod.unsigned (N.v43417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43417 s i)) at 1.
  unfold R.v43417, N.v43417.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43418 (s : N.State) (i : N.Inputs) :
  R.v43418 (state s) (inputs i) = Zmod.unsigned (N.v43418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43418 s i)) at 1.
  unfold R.v43418, N.v43418.
  rewrite ?node_10857.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43419 (s : N.State) (i : N.Inputs) :
  R.v43419 (state s) (inputs i) = Zmod.unsigned (N.v43419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43419 s i)) at 1.
  unfold R.v43419, N.v43419.
  unfold R.v6, N.v6.
  rewrite ?node_10853.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43420 (s : N.State) (i : N.Inputs) :
  R.v43420 (state s) (inputs i) = Zmod.unsigned (N.v43420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43420 s i)) at 1.
  unfold R.v43420, N.v43420.
  unfold R.v6, N.v6.
  rewrite ?node_10850.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43421 (s : N.State) (i : N.Inputs) :
  R.v43421 (state s) (inputs i) = Zmod.unsigned (N.v43421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43421 s i)) at 1.
  unfold R.v43421, N.v43421.
  rewrite ?node_43419.
  rewrite ?node_43420.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43422 (s : N.State) (i : N.Inputs) :
  R.v43422 (state s) (inputs i) = Zmod.unsigned (N.v43422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43422 s i)) at 1.
  unfold R.v43422, N.v43422.
  unfold R.v16484, N.v16484.
  rewrite ?node_43421.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43423 (s : N.State) (i : N.Inputs) :
  R.v43423 (state s) (inputs i) = Zmod.unsigned (N.v43423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43423 s i)) at 1.
  unfold R.v43423, N.v43423.
  rewrite ?node_43418.
  rewrite ?node_43422.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43424 (s : N.State) (i : N.Inputs) :
  R.v43424 (state s) (inputs i) = Zmod.unsigned (N.v43424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43424 s i)) at 1.
  unfold R.v43424, N.v43424.
  unfold R.v6, N.v6.
  rewrite ?node_43423.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43425 (s : N.State) (i : N.Inputs) :
  R.v43425 (state s) (inputs i) = Zmod.unsigned (N.v43425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43425 s i)) at 1.
  unfold R.v43425, N.v43425.
  rewrite ?node_10858.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43426 (s : N.State) (i : N.Inputs) :
  R.v43426 (state s) (inputs i) = Zmod.unsigned (N.v43426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43426 s i)) at 1.
  unfold R.v43426, N.v43426.
  unfold R.v6, N.v6.
  rewrite ?node_11026.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43427 (s : N.State) (i : N.Inputs) :
  R.v43427 (state s) (inputs i) = Zmod.unsigned (N.v43427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43427 s i)) at 1.
  unfold R.v43427, N.v43427.
  rewrite ?node_43425.
  rewrite ?node_43426.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43428 (s : N.State) (i : N.Inputs) :
  R.v43428 (state s) (inputs i) = Zmod.unsigned (N.v43428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43428 s i)) at 1.
  unfold R.v43428, N.v43428.
  rewrite ?node_43424.
  rewrite ?node_43427.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43429 (s : N.State) (i : N.Inputs) :
  R.v43429 (state s) (inputs i) = Zmod.unsigned (N.v43429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43429 s i)) at 1.
  unfold R.v43429, N.v43429.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43430 (s : N.State) (i : N.Inputs) :
  R.v43430 (state s) (inputs i) = Zmod.unsigned (N.v43430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43430 s i)) at 1.
  unfold R.v43430, N.v43430.
  rewrite ?node_10865.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43431 (s : N.State) (i : N.Inputs) :
  R.v43431 (state s) (inputs i) = Zmod.unsigned (N.v43431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43431 s i)) at 1.
  unfold R.v43431, N.v43431.
  unfold R.v6, N.v6.
  rewrite ?node_10861.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43432 (s : N.State) (i : N.Inputs) :
  R.v43432 (state s) (inputs i) = Zmod.unsigned (N.v43432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43432 s i)) at 1.
  unfold R.v43432, N.v43432.
  unfold R.v6, N.v6.
  rewrite ?node_10858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43433 (s : N.State) (i : N.Inputs) :
  R.v43433 (state s) (inputs i) = Zmod.unsigned (N.v43433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43433 s i)) at 1.
  unfold R.v43433, N.v43433.
  rewrite ?node_43431.
  rewrite ?node_43432.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43434 (s : N.State) (i : N.Inputs) :
  R.v43434 (state s) (inputs i) = Zmod.unsigned (N.v43434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43434 s i)) at 1.
  unfold R.v43434, N.v43434.
  unfold R.v16484, N.v16484.
  rewrite ?node_43433.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43435 (s : N.State) (i : N.Inputs) :
  R.v43435 (state s) (inputs i) = Zmod.unsigned (N.v43435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43435 s i)) at 1.
  unfold R.v43435, N.v43435.
  rewrite ?node_43430.
  rewrite ?node_43434.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43436 (s : N.State) (i : N.Inputs) :
  R.v43436 (state s) (inputs i) = Zmod.unsigned (N.v43436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43436 s i)) at 1.
  unfold R.v43436, N.v43436.
  unfold R.v6, N.v6.
  rewrite ?node_43435.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43437 (s : N.State) (i : N.Inputs) :
  R.v43437 (state s) (inputs i) = Zmod.unsigned (N.v43437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43437 s i)) at 1.
  unfold R.v43437, N.v43437.
  rewrite ?node_10866.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43438 (s : N.State) (i : N.Inputs) :
  R.v43438 (state s) (inputs i) = Zmod.unsigned (N.v43438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43438 s i)) at 1.
  unfold R.v43438, N.v43438.
  unfold R.v6, N.v6.
  rewrite ?node_11055.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43439 (s : N.State) (i : N.Inputs) :
  R.v43439 (state s) (inputs i) = Zmod.unsigned (N.v43439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43439 s i)) at 1.
  unfold R.v43439, N.v43439.
  rewrite ?node_43437.
  rewrite ?node_43438.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43440 (s : N.State) (i : N.Inputs) :
  R.v43440 (state s) (inputs i) = Zmod.unsigned (N.v43440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43440 s i)) at 1.
  unfold R.v43440, N.v43440.
  rewrite ?node_43436.
  rewrite ?node_43439.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43441 (s : N.State) (i : N.Inputs) :
  R.v43441 (state s) (inputs i) = Zmod.unsigned (N.v43441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43441 s i)) at 1.
  unfold R.v43441, N.v43441.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43442 (s : N.State) (i : N.Inputs) :
  R.v43442 (state s) (inputs i) = Zmod.unsigned (N.v43442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43442 s i)) at 1.
  unfold R.v43442, N.v43442.
  rewrite ?node_10954.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43443 (s : N.State) (i : N.Inputs) :
  R.v43443 (state s) (inputs i) = Zmod.unsigned (N.v43443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43443 s i)) at 1.
  unfold R.v43443, N.v43443.
  rewrite ?node_10950.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43444 (s : N.State) (i : N.Inputs) :
  R.v43444 (state s) (inputs i) = Zmod.unsigned (N.v43444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43444 s i)) at 1.
  unfold R.v43444, N.v43444.
  rewrite ?node_10942.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43445 (s : N.State) (i : N.Inputs) :
  R.v43445 (state s) (inputs i) = Zmod.unsigned (N.v43445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43445 s i)) at 1.
  unfold R.v43445, N.v43445.
  unfold R.v6, N.v6.
  rewrite ?node_10934.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43446 (s : N.State) (i : N.Inputs) :
  R.v43446 (state s) (inputs i) = Zmod.unsigned (N.v43446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43446 s i)) at 1.
  unfold R.v43446, N.v43446.
  unfold R.v6, N.v6.
  rewrite ?node_10927.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43447 (s : N.State) (i : N.Inputs) :
  R.v43447 (state s) (inputs i) = Zmod.unsigned (N.v43447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43447 s i)) at 1.
  unfold R.v43447, N.v43447.
  rewrite ?node_43445.
  rewrite ?node_43446.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43448 (s : N.State) (i : N.Inputs) :
  R.v43448 (state s) (inputs i) = Zmod.unsigned (N.v43448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43448 s i)) at 1.
  unfold R.v43448, N.v43448.
  unfold R.v16484, N.v16484.
  rewrite ?node_43447.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43449 (s : N.State) (i : N.Inputs) :
  R.v43449 (state s) (inputs i) = Zmod.unsigned (N.v43449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43449 s i)) at 1.
  unfold R.v43449, N.v43449.
  rewrite ?node_43442.
  rewrite ?node_43443.
  rewrite ?node_43444.
  rewrite ?node_43448.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43450 (s : N.State) (i : N.Inputs) :
  R.v43450 (state s) (inputs i) = Zmod.unsigned (N.v43450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43450 s i)) at 1.
  unfold R.v43450, N.v43450.
  unfold R.v6, N.v6.
  rewrite ?node_43449.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43451 (s : N.State) (i : N.Inputs) :
  R.v43451 (state s) (inputs i) = Zmod.unsigned (N.v43451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43451 s i)) at 1.
  unfold R.v43451, N.v43451.
  rewrite ?node_10955.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43452 (s : N.State) (i : N.Inputs) :
  R.v43452 (state s) (inputs i) = Zmod.unsigned (N.v43452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43452 s i)) at 1.
  unfold R.v43452, N.v43452.
  unfold R.v6, N.v6.
  rewrite ?node_11115.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43453 (s : N.State) (i : N.Inputs) :
  R.v43453 (state s) (inputs i) = Zmod.unsigned (N.v43453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43453 s i)) at 1.
  unfold R.v43453, N.v43453.
  unfold R.v6, N.v6.
  rewrite ?node_11199.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43454 (s : N.State) (i : N.Inputs) :
  R.v43454 (state s) (inputs i) = Zmod.unsigned (N.v43454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43454 s i)) at 1.
  unfold R.v43454, N.v43454.
  rewrite ?node_43451.
  rewrite ?node_43452.
  rewrite ?node_43453.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43455 (s : N.State) (i : N.Inputs) :
  R.v43455 (state s) (inputs i) = Zmod.unsigned (N.v43455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43455 s i)) at 1.
  unfold R.v43455, N.v43455.
  rewrite ?node_43450.
  rewrite ?node_43454.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43456 (s : N.State) (i : N.Inputs) :
  R.v43456 (state s) (inputs i) = Zmod.unsigned (N.v43456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43456 s i)) at 1.
  unfold R.v43456, N.v43456.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43457 (s : N.State) (i : N.Inputs) :
  R.v43457 (state s) (inputs i) = Zmod.unsigned (N.v43457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43457 s i)) at 1.
  unfold R.v43457, N.v43457.
  rewrite ?node_10942.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43458 (s : N.State) (i : N.Inputs) :
  R.v43458 (state s) (inputs i) = Zmod.unsigned (N.v43458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43458 s i)) at 1.
  unfold R.v43458, N.v43458.
  unfold R.v6, N.v6.
  rewrite ?node_10934.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43459 (s : N.State) (i : N.Inputs) :
  R.v43459 (state s) (inputs i) = Zmod.unsigned (N.v43459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43459 s i)) at 1.
  unfold R.v43459, N.v43459.
  unfold R.v6, N.v6.
  rewrite ?node_10927.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43460 (s : N.State) (i : N.Inputs) :
  R.v43460 (state s) (inputs i) = Zmod.unsigned (N.v43460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43460 s i)) at 1.
  unfold R.v43460, N.v43460.
  rewrite ?node_43458.
  rewrite ?node_43459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43461 (s : N.State) (i : N.Inputs) :
  R.v43461 (state s) (inputs i) = Zmod.unsigned (N.v43461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43461 s i)) at 1.
  unfold R.v43461, N.v43461.
  unfold R.v16484, N.v16484.
  rewrite ?node_43460.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43462 (s : N.State) (i : N.Inputs) :
  R.v43462 (state s) (inputs i) = Zmod.unsigned (N.v43462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43462 s i)) at 1.
  unfold R.v43462, N.v43462.
  rewrite ?node_43457.
  rewrite ?node_43461.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43463 (s : N.State) (i : N.Inputs) :
  R.v43463 (state s) (inputs i) = Zmod.unsigned (N.v43463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43463 s i)) at 1.
  unfold R.v43463, N.v43463.
  unfold R.v6, N.v6.
  rewrite ?node_43462.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43464 (s : N.State) (i : N.Inputs) :
  R.v43464 (state s) (inputs i) = Zmod.unsigned (N.v43464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43464 s i)) at 1.
  unfold R.v43464, N.v43464.
  rewrite ?node_10943.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43465 (s : N.State) (i : N.Inputs) :
  R.v43465 (state s) (inputs i) = Zmod.unsigned (N.v43465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43465 s i)) at 1.
  unfold R.v43465, N.v43465.
  unfold R.v6, N.v6.
  rewrite ?node_11115.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43466 (s : N.State) (i : N.Inputs) :
  R.v43466 (state s) (inputs i) = Zmod.unsigned (N.v43466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43466 s i)) at 1.
  unfold R.v43466, N.v43466.
  rewrite ?node_43464.
  rewrite ?node_43465.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43467 (s : N.State) (i : N.Inputs) :
  R.v43467 (state s) (inputs i) = Zmod.unsigned (N.v43467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43467 s i)) at 1.
  unfold R.v43467, N.v43467.
  rewrite ?node_43463.
  rewrite ?node_43466.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43468 (s : N.State) (i : N.Inputs) :
  R.v43468 (state s) (inputs i) = Zmod.unsigned (N.v43468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43468 s i)) at 1.
  unfold R.v43468, N.v43468.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43469 (s : N.State) (i : N.Inputs) :
  R.v43469 (state s) (inputs i) = Zmod.unsigned (N.v43469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43469 s i)) at 1.
  unfold R.v43469, N.v43469.
  rewrite ?node_10954.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43470 (s : N.State) (i : N.Inputs) :
  R.v43470 (state s) (inputs i) = Zmod.unsigned (N.v43470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43470 s i)) at 1.
  unfold R.v43470, N.v43470.
  unfold R.v6, N.v6.
  rewrite ?node_10950.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43471 (s : N.State) (i : N.Inputs) :
  R.v43471 (state s) (inputs i) = Zmod.unsigned (N.v43471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43471 s i)) at 1.
  unfold R.v43471, N.v43471.
  unfold R.v6, N.v6.
  rewrite ?node_10943.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43472 (s : N.State) (i : N.Inputs) :
  R.v43472 (state s) (inputs i) = Zmod.unsigned (N.v43472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43472 s i)) at 1.
  unfold R.v43472, N.v43472.
  rewrite ?node_43470.
  rewrite ?node_43471.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43473 (s : N.State) (i : N.Inputs) :
  R.v43473 (state s) (inputs i) = Zmod.unsigned (N.v43473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43473 s i)) at 1.
  unfold R.v43473, N.v43473.
  unfold R.v16484, N.v16484.
  rewrite ?node_43472.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43474 (s : N.State) (i : N.Inputs) :
  R.v43474 (state s) (inputs i) = Zmod.unsigned (N.v43474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43474 s i)) at 1.
  unfold R.v43474, N.v43474.
  rewrite ?node_43469.
  rewrite ?node_43473.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43475 (s : N.State) (i : N.Inputs) :
  R.v43475 (state s) (inputs i) = Zmod.unsigned (N.v43475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43475 s i)) at 1.
  unfold R.v43475, N.v43475.
  unfold R.v6, N.v6.
  rewrite ?node_43474.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43476 (s : N.State) (i : N.Inputs) :
  R.v43476 (state s) (inputs i) = Zmod.unsigned (N.v43476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43476 s i)) at 1.
  unfold R.v43476, N.v43476.
  rewrite ?node_10955.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43477 (s : N.State) (i : N.Inputs) :
  R.v43477 (state s) (inputs i) = Zmod.unsigned (N.v43477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43477 s i)) at 1.
  unfold R.v43477, N.v43477.
  unfold R.v6, N.v6.
  rewrite ?node_11199.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43478 (s : N.State) (i : N.Inputs) :
  R.v43478 (state s) (inputs i) = Zmod.unsigned (N.v43478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43478 s i)) at 1.
  unfold R.v43478, N.v43478.
  rewrite ?node_43476.
  rewrite ?node_43477.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43479 (s : N.State) (i : N.Inputs) :
  R.v43479 (state s) (inputs i) = Zmod.unsigned (N.v43479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43479 s i)) at 1.
  unfold R.v43479, N.v43479.
  rewrite ?node_43475.
  rewrite ?node_43478.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43480 (s : N.State) (i : N.Inputs) :
  R.v43480 (state s) (inputs i) = Zmod.unsigned (N.v43480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43480 s i)) at 1.
  unfold R.v43480, N.v43480.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43481 (s : N.State) (i : N.Inputs) :
  R.v43481 (state s) (inputs i) = Zmod.unsigned (N.v43481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43481 s i)) at 1.
  unfold R.v43481, N.v43481.
  rewrite ?node_10989.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43482 (s : N.State) (i : N.Inputs) :
  R.v43482 (state s) (inputs i) = Zmod.unsigned (N.v43482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43482 s i)) at 1.
  unfold R.v43482, N.v43482.
  rewrite ?node_10985.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43483 (s : N.State) (i : N.Inputs) :
  R.v43483 (state s) (inputs i) = Zmod.unsigned (N.v43483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43483 s i)) at 1.
  unfold R.v43483, N.v43483.
  rewrite ?node_10977.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43484 (s : N.State) (i : N.Inputs) :
  R.v43484 (state s) (inputs i) = Zmod.unsigned (N.v43484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43484 s i)) at 1.
  unfold R.v43484, N.v43484.
  unfold R.v6, N.v6.
  rewrite ?node_10969.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43485 (s : N.State) (i : N.Inputs) :
  R.v43485 (state s) (inputs i) = Zmod.unsigned (N.v43485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43485 s i)) at 1.
  unfold R.v43485, N.v43485.
  unfold R.v6, N.v6.
  rewrite ?node_10962.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43486 (s : N.State) (i : N.Inputs) :
  R.v43486 (state s) (inputs i) = Zmod.unsigned (N.v43486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43486 s i)) at 1.
  unfold R.v43486, N.v43486.
  rewrite ?node_43484.
  rewrite ?node_43485.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43487 (s : N.State) (i : N.Inputs) :
  R.v43487 (state s) (inputs i) = Zmod.unsigned (N.v43487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43487 s i)) at 1.
  unfold R.v43487, N.v43487.
  unfold R.v16484, N.v16484.
  rewrite ?node_43486.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43488 (s : N.State) (i : N.Inputs) :
  R.v43488 (state s) (inputs i) = Zmod.unsigned (N.v43488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43488 s i)) at 1.
  unfold R.v43488, N.v43488.
  rewrite ?node_43481.
  rewrite ?node_43482.
  rewrite ?node_43483.
  rewrite ?node_43487.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43489 (s : N.State) (i : N.Inputs) :
  R.v43489 (state s) (inputs i) = Zmod.unsigned (N.v43489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43489 s i)) at 1.
  unfold R.v43489, N.v43489.
  unfold R.v6, N.v6.
  rewrite ?node_43488.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43490 (s : N.State) (i : N.Inputs) :
  R.v43490 (state s) (inputs i) = Zmod.unsigned (N.v43490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43490 s i)) at 1.
  unfold R.v43490, N.v43490.
  rewrite ?node_10990.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43491 (s : N.State) (i : N.Inputs) :
  R.v43491 (state s) (inputs i) = Zmod.unsigned (N.v43491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43491 s i)) at 1.
  unfold R.v43491, N.v43491.
  unfold R.v6, N.v6.
  rewrite ?node_11150.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43492 (s : N.State) (i : N.Inputs) :
  R.v43492 (state s) (inputs i) = Zmod.unsigned (N.v43492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43492 s i)) at 1.
  unfold R.v43492, N.v43492.
  unfold R.v6, N.v6.
  rewrite ?node_11202.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43493 (s : N.State) (i : N.Inputs) :
  R.v43493 (state s) (inputs i) = Zmod.unsigned (N.v43493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43493 s i)) at 1.
  unfold R.v43493, N.v43493.
  rewrite ?node_43490.
  rewrite ?node_43491.
  rewrite ?node_43492.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43494 (s : N.State) (i : N.Inputs) :
  R.v43494 (state s) (inputs i) = Zmod.unsigned (N.v43494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43494 s i)) at 1.
  unfold R.v43494, N.v43494.
  rewrite ?node_43489.
  rewrite ?node_43493.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43495 (s : N.State) (i : N.Inputs) :
  R.v43495 (state s) (inputs i) = Zmod.unsigned (N.v43495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43495 s i)) at 1.
  unfold R.v43495, N.v43495.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43496 (s : N.State) (i : N.Inputs) :
  R.v43496 (state s) (inputs i) = Zmod.unsigned (N.v43496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43496 s i)) at 1.
  unfold R.v43496, N.v43496.
  rewrite ?node_10977.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43497 (s : N.State) (i : N.Inputs) :
  R.v43497 (state s) (inputs i) = Zmod.unsigned (N.v43497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43497 s i)) at 1.
  unfold R.v43497, N.v43497.
  unfold R.v6, N.v6.
  rewrite ?node_10969.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43498 (s : N.State) (i : N.Inputs) :
  R.v43498 (state s) (inputs i) = Zmod.unsigned (N.v43498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43498 s i)) at 1.
  unfold R.v43498, N.v43498.
  unfold R.v6, N.v6.
  rewrite ?node_10962.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43499 (s : N.State) (i : N.Inputs) :
  R.v43499 (state s) (inputs i) = Zmod.unsigned (N.v43499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43499 s i)) at 1.
  unfold R.v43499, N.v43499.
  rewrite ?node_43497.
  rewrite ?node_43498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43500 (s : N.State) (i : N.Inputs) :
  R.v43500 (state s) (inputs i) = Zmod.unsigned (N.v43500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43500 s i)) at 1.
  unfold R.v43500, N.v43500.
  unfold R.v16484, N.v16484.
  rewrite ?node_43499.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43501 (s : N.State) (i : N.Inputs) :
  R.v43501 (state s) (inputs i) = Zmod.unsigned (N.v43501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43501 s i)) at 1.
  unfold R.v43501, N.v43501.
  rewrite ?node_43496.
  rewrite ?node_43500.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43502 (s : N.State) (i : N.Inputs) :
  R.v43502 (state s) (inputs i) = Zmod.unsigned (N.v43502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43502 s i)) at 1.
  unfold R.v43502, N.v43502.
  unfold R.v6, N.v6.
  rewrite ?node_43501.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43503 (s : N.State) (i : N.Inputs) :
  R.v43503 (state s) (inputs i) = Zmod.unsigned (N.v43503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43503 s i)) at 1.
  unfold R.v43503, N.v43503.
  rewrite ?node_10978.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43504 (s : N.State) (i : N.Inputs) :
  R.v43504 (state s) (inputs i) = Zmod.unsigned (N.v43504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43504 s i)) at 1.
  unfold R.v43504, N.v43504.
  unfold R.v6, N.v6.
  rewrite ?node_11150.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43505 (s : N.State) (i : N.Inputs) :
  R.v43505 (state s) (inputs i) = Zmod.unsigned (N.v43505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43505 s i)) at 1.
  unfold R.v43505, N.v43505.
  rewrite ?node_43503.
  rewrite ?node_43504.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43506 (s : N.State) (i : N.Inputs) :
  R.v43506 (state s) (inputs i) = Zmod.unsigned (N.v43506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43506 s i)) at 1.
  unfold R.v43506, N.v43506.
  rewrite ?node_43502.
  rewrite ?node_43505.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43507 (s : N.State) (i : N.Inputs) :
  R.v43507 (state s) (inputs i) = Zmod.unsigned (N.v43507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43507 s i)) at 1.
  unfold R.v43507, N.v43507.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43508 (s : N.State) (i : N.Inputs) :
  R.v43508 (state s) (inputs i) = Zmod.unsigned (N.v43508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43508 s i)) at 1.
  unfold R.v43508, N.v43508.
  rewrite ?node_10989.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43509 (s : N.State) (i : N.Inputs) :
  R.v43509 (state s) (inputs i) = Zmod.unsigned (N.v43509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43509 s i)) at 1.
  unfold R.v43509, N.v43509.
  unfold R.v6, N.v6.
  rewrite ?node_10985.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43510 (s : N.State) (i : N.Inputs) :
  R.v43510 (state s) (inputs i) = Zmod.unsigned (N.v43510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43510 s i)) at 1.
  unfold R.v43510, N.v43510.
  unfold R.v6, N.v6.
  rewrite ?node_10978.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43511 (s : N.State) (i : N.Inputs) :
  R.v43511 (state s) (inputs i) = Zmod.unsigned (N.v43511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43511 s i)) at 1.
  unfold R.v43511, N.v43511.
  rewrite ?node_43509.
  rewrite ?node_43510.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43512 (s : N.State) (i : N.Inputs) :
  R.v43512 (state s) (inputs i) = Zmod.unsigned (N.v43512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43512 s i)) at 1.
  unfold R.v43512, N.v43512.
  unfold R.v16484, N.v16484.
  rewrite ?node_43511.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43513 (s : N.State) (i : N.Inputs) :
  R.v43513 (state s) (inputs i) = Zmod.unsigned (N.v43513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43513 s i)) at 1.
  unfold R.v43513, N.v43513.
  rewrite ?node_43508.
  rewrite ?node_43512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43514 (s : N.State) (i : N.Inputs) :
  R.v43514 (state s) (inputs i) = Zmod.unsigned (N.v43514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43514 s i)) at 1.
  unfold R.v43514, N.v43514.
  unfold R.v6, N.v6.
  rewrite ?node_43513.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43515 (s : N.State) (i : N.Inputs) :
  R.v43515 (state s) (inputs i) = Zmod.unsigned (N.v43515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43515 s i)) at 1.
  unfold R.v43515, N.v43515.
  rewrite ?node_10990.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43516 (s : N.State) (i : N.Inputs) :
  R.v43516 (state s) (inputs i) = Zmod.unsigned (N.v43516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43516 s i)) at 1.
  unfold R.v43516, N.v43516.
  unfold R.v6, N.v6.
  rewrite ?node_11202.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43517 (s : N.State) (i : N.Inputs) :
  R.v43517 (state s) (inputs i) = Zmod.unsigned (N.v43517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43517 s i)) at 1.
  unfold R.v43517, N.v43517.
  rewrite ?node_43515.
  rewrite ?node_43516.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43518 (s : N.State) (i : N.Inputs) :
  R.v43518 (state s) (inputs i) = Zmod.unsigned (N.v43518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43518 s i)) at 1.
  unfold R.v43518, N.v43518.
  rewrite ?node_43514.
  rewrite ?node_43517.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43519 (s : N.State) (i : N.Inputs) :
  R.v43519 (state s) (inputs i) = Zmod.unsigned (N.v43519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43519 s i)) at 1.
  unfold R.v43519, N.v43519.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43520 (s : N.State) (i : N.Inputs) :
  R.v43520 (state s) (inputs i) = Zmod.unsigned (N.v43520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43520 s i)) at 1.
  unfold R.v43520, N.v43520.
  rewrite ?node_11006.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43521 (s : N.State) (i : N.Inputs) :
  R.v43521 (state s) (inputs i) = Zmod.unsigned (N.v43521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43521 s i)) at 1.
  unfold R.v43521, N.v43521.
  rewrite ?node_11002.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43522 (s : N.State) (i : N.Inputs) :
  R.v43522 (state s) (inputs i) = Zmod.unsigned (N.v43522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43522 s i)) at 1.
  unfold R.v43522, N.v43522.
  rewrite ?node_10998.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43523 (s : N.State) (i : N.Inputs) :
  R.v43523 (state s) (inputs i) = Zmod.unsigned (N.v43523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43523 s i)) at 1.
  unfold R.v43523, N.v43523.
  unfold R.v6, N.v6.
  rewrite ?node_10994.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43524 (s : N.State) (i : N.Inputs) :
  R.v43524 (state s) (inputs i) = Zmod.unsigned (N.v43524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43524 s i)) at 1.
  unfold R.v43524, N.v43524.
  unfold R.v6, N.v6.
  rewrite !state_r1286_nr_5F1286.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1286_nr_5F1286 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43525 (s : N.State) (i : N.Inputs) :
  R.v43525 (state s) (inputs i) = Zmod.unsigned (N.v43525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43525 s i)) at 1.
  unfold R.v43525, N.v43525.
  rewrite ?node_43523.
  rewrite ?node_43524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43526 (s : N.State) (i : N.Inputs) :
  R.v43526 (state s) (inputs i) = Zmod.unsigned (N.v43526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43526 s i)) at 1.
  unfold R.v43526, N.v43526.
  unfold R.v16484, N.v16484.
  rewrite ?node_43525.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43527 (s : N.State) (i : N.Inputs) :
  R.v43527 (state s) (inputs i) = Zmod.unsigned (N.v43527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43527 s i)) at 1.
  unfold R.v43527, N.v43527.
  rewrite ?node_43520.
  rewrite ?node_43521.
  rewrite ?node_43522.
  rewrite ?node_43526.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43528 (s : N.State) (i : N.Inputs) :
  R.v43528 (state s) (inputs i) = Zmod.unsigned (N.v43528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43528 s i)) at 1.
  unfold R.v43528, N.v43528.
  unfold R.v6, N.v6.
  rewrite ?node_43527.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43529 (s : N.State) (i : N.Inputs) :
  R.v43529 (state s) (inputs i) = Zmod.unsigned (N.v43529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43529 s i)) at 1.
  unfold R.v43529, N.v43529.
  rewrite ?node_11007.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43530 (s : N.State) (i : N.Inputs) :
  R.v43530 (state s) (inputs i) = Zmod.unsigned (N.v43530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43530 s i)) at 1.
  unfold R.v43530, N.v43530.
  unfold R.v6, N.v6.
  rewrite ?node_11170.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43531 (s : N.State) (i : N.Inputs) :
  R.v43531 (state s) (inputs i) = Zmod.unsigned (N.v43531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43531 s i)) at 1.
  unfold R.v43531, N.v43531.
  unfold R.v6, N.v6.
  rewrite ?node_11206.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43532 (s : N.State) (i : N.Inputs) :
  R.v43532 (state s) (inputs i) = Zmod.unsigned (N.v43532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43532 s i)) at 1.
  unfold R.v43532, N.v43532.
  rewrite ?node_43529.
  rewrite ?node_43530.
  rewrite ?node_43531.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43533 (s : N.State) (i : N.Inputs) :
  R.v43533 (state s) (inputs i) = Zmod.unsigned (N.v43533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43533 s i)) at 1.
  unfold R.v43533, N.v43533.
  rewrite ?node_43528.
  rewrite ?node_43532.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43534 (s : N.State) (i : N.Inputs) :
  R.v43534 (state s) (inputs i) = Zmod.unsigned (N.v43534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43534 s i)) at 1.
  unfold R.v43534, N.v43534.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43535 (s : N.State) (i : N.Inputs) :
  R.v43535 (state s) (inputs i) = Zmod.unsigned (N.v43535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43535 s i)) at 1.
  unfold R.v43535, N.v43535.
  rewrite ?node_10998.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43536 (s : N.State) (i : N.Inputs) :
  R.v43536 (state s) (inputs i) = Zmod.unsigned (N.v43536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43536 s i)) at 1.
  unfold R.v43536, N.v43536.
  unfold R.v6, N.v6.
  rewrite ?node_10994.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43537 (s : N.State) (i : N.Inputs) :
  R.v43537 (state s) (inputs i) = Zmod.unsigned (N.v43537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43537 s i)) at 1.
  unfold R.v43537, N.v43537.
  unfold R.v6, N.v6.
  rewrite !state_r1286_nr_5F1286.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1286_nr_5F1286 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43538 (s : N.State) (i : N.Inputs) :
  R.v43538 (state s) (inputs i) = Zmod.unsigned (N.v43538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43538 s i)) at 1.
  unfold R.v43538, N.v43538.
  rewrite ?node_43536.
  rewrite ?node_43537.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43539 (s : N.State) (i : N.Inputs) :
  R.v43539 (state s) (inputs i) = Zmod.unsigned (N.v43539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43539 s i)) at 1.
  unfold R.v43539, N.v43539.
  unfold R.v16484, N.v16484.
  rewrite ?node_43538.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43540 (s : N.State) (i : N.Inputs) :
  R.v43540 (state s) (inputs i) = Zmod.unsigned (N.v43540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43540 s i)) at 1.
  unfold R.v43540, N.v43540.
  rewrite ?node_43535.
  rewrite ?node_43539.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43541 (s : N.State) (i : N.Inputs) :
  R.v43541 (state s) (inputs i) = Zmod.unsigned (N.v43541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43541 s i)) at 1.
  unfold R.v43541, N.v43541.
  unfold R.v6, N.v6.
  rewrite ?node_43540.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43542 (s : N.State) (i : N.Inputs) :
  R.v43542 (state s) (inputs i) = Zmod.unsigned (N.v43542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43542 s i)) at 1.
  unfold R.v43542, N.v43542.
  rewrite ?node_10999.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43543 (s : N.State) (i : N.Inputs) :
  R.v43543 (state s) (inputs i) = Zmod.unsigned (N.v43543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43543 s i)) at 1.
  unfold R.v43543, N.v43543.
  unfold R.v6, N.v6.
  rewrite ?node_11170.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43544 (s : N.State) (i : N.Inputs) :
  R.v43544 (state s) (inputs i) = Zmod.unsigned (N.v43544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43544 s i)) at 1.
  unfold R.v43544, N.v43544.
  rewrite ?node_43542.
  rewrite ?node_43543.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43545 (s : N.State) (i : N.Inputs) :
  R.v43545 (state s) (inputs i) = Zmod.unsigned (N.v43545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43545 s i)) at 1.
  unfold R.v43545, N.v43545.
  rewrite ?node_43541.
  rewrite ?node_43544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43546 (s : N.State) (i : N.Inputs) :
  R.v43546 (state s) (inputs i) = Zmod.unsigned (N.v43546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43546 s i)) at 1.
  unfold R.v43546, N.v43546.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43547 (s : N.State) (i : N.Inputs) :
  R.v43547 (state s) (inputs i) = Zmod.unsigned (N.v43547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43547 s i)) at 1.
  unfold R.v43547, N.v43547.
  rewrite ?node_11006.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43548 (s : N.State) (i : N.Inputs) :
  R.v43548 (state s) (inputs i) = Zmod.unsigned (N.v43548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43548 s i)) at 1.
  unfold R.v43548, N.v43548.
  unfold R.v6, N.v6.
  rewrite ?node_11002.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43549 (s : N.State) (i : N.Inputs) :
  R.v43549 (state s) (inputs i) = Zmod.unsigned (N.v43549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43549 s i)) at 1.
  unfold R.v43549, N.v43549.
  unfold R.v6, N.v6.
  rewrite ?node_10999.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43550 (s : N.State) (i : N.Inputs) :
  R.v43550 (state s) (inputs i) = Zmod.unsigned (N.v43550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43550 s i)) at 1.
  unfold R.v43550, N.v43550.
  rewrite ?node_43548.
  rewrite ?node_43549.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43551 (s : N.State) (i : N.Inputs) :
  R.v43551 (state s) (inputs i) = Zmod.unsigned (N.v43551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43551 s i)) at 1.
  unfold R.v43551, N.v43551.
  unfold R.v16484, N.v16484.
  rewrite ?node_43550.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43552 (s : N.State) (i : N.Inputs) :
  R.v43552 (state s) (inputs i) = Zmod.unsigned (N.v43552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43552 s i)) at 1.
  unfold R.v43552, N.v43552.
  rewrite ?node_43547.
  rewrite ?node_43551.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43553 (s : N.State) (i : N.Inputs) :
  R.v43553 (state s) (inputs i) = Zmod.unsigned (N.v43553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43553 s i)) at 1.
  unfold R.v43553, N.v43553.
  unfold R.v6, N.v6.
  rewrite ?node_43552.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43554 (s : N.State) (i : N.Inputs) :
  R.v43554 (state s) (inputs i) = Zmod.unsigned (N.v43554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43554 s i)) at 1.
  unfold R.v43554, N.v43554.
  rewrite ?node_11007.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43555 (s : N.State) (i : N.Inputs) :
  R.v43555 (state s) (inputs i) = Zmod.unsigned (N.v43555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43555 s i)) at 1.
  unfold R.v43555, N.v43555.
  unfold R.v6, N.v6.
  rewrite ?node_11206.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43556 (s : N.State) (i : N.Inputs) :
  R.v43556 (state s) (inputs i) = Zmod.unsigned (N.v43556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43556 s i)) at 1.
  unfold R.v43556, N.v43556.
  rewrite ?node_43554.
  rewrite ?node_43555.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43557 (s : N.State) (i : N.Inputs) :
  R.v43557 (state s) (inputs i) = Zmod.unsigned (N.v43557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43557 s i)) at 1.
  unfold R.v43557, N.v43557.
  rewrite ?node_43553.
  rewrite ?node_43556.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43558 (s : N.State) (i : N.Inputs) :
  R.v43558 (state s) (inputs i) = Zmod.unsigned (N.v43558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43558 s i)) at 1.
  unfold R.v43558, N.v43558.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43559 (s : N.State) (i : N.Inputs) :
  R.v43559 (state s) (inputs i) = Zmod.unsigned (N.v43559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43559 s i)) at 1.
  unfold R.v43559, N.v43559.
  rewrite ?node_11026.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43560 (s : N.State) (i : N.Inputs) :
  R.v43560 (state s) (inputs i) = Zmod.unsigned (N.v43560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43560 s i)) at 1.
  unfold R.v43560, N.v43560.
  rewrite ?node_11022.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43561 (s : N.State) (i : N.Inputs) :
  R.v43561 (state s) (inputs i) = Zmod.unsigned (N.v43561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43561 s i)) at 1.
  unfold R.v43561, N.v43561.
  rewrite ?node_11018.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43562 (s : N.State) (i : N.Inputs) :
  R.v43562 (state s) (inputs i) = Zmod.unsigned (N.v43562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43562 s i)) at 1.
  unfold R.v43562, N.v43562.
  unfold R.v6, N.v6.
  rewrite ?node_11014.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43563 (s : N.State) (i : N.Inputs) :
  R.v43563 (state s) (inputs i) = Zmod.unsigned (N.v43563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43563 s i)) at 1.
  unfold R.v43563, N.v43563.
  unfold R.v6, N.v6.
  rewrite ?node_11011.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43564 (s : N.State) (i : N.Inputs) :
  R.v43564 (state s) (inputs i) = Zmod.unsigned (N.v43564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43564 s i)) at 1.
  unfold R.v43564, N.v43564.
  rewrite ?node_43562.
  rewrite ?node_43563.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43565 (s : N.State) (i : N.Inputs) :
  R.v43565 (state s) (inputs i) = Zmod.unsigned (N.v43565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43565 s i)) at 1.
  unfold R.v43565, N.v43565.
  unfold R.v16484, N.v16484.
  rewrite ?node_43564.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43566 (s : N.State) (i : N.Inputs) :
  R.v43566 (state s) (inputs i) = Zmod.unsigned (N.v43566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43566 s i)) at 1.
  unfold R.v43566, N.v43566.
  rewrite ?node_43559.
  rewrite ?node_43560.
  rewrite ?node_43561.
  rewrite ?node_43565.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43567 (s : N.State) (i : N.Inputs) :
  R.v43567 (state s) (inputs i) = Zmod.unsigned (N.v43567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43567 s i)) at 1.
  unfold R.v43567, N.v43567.
  unfold R.v6, N.v6.
  rewrite ?node_43566.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43568 (s : N.State) (i : N.Inputs) :
  R.v43568 (state s) (inputs i) = Zmod.unsigned (N.v43568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43568 s i)) at 1.
  unfold R.v43568, N.v43568.
  rewrite ?node_11027.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43569 (s : N.State) (i : N.Inputs) :
  R.v43569 (state s) (inputs i) = Zmod.unsigned (N.v43569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43569 s i)) at 1.
  unfold R.v43569, N.v43569.
  unfold R.v6, N.v6.
  rewrite ?node_11190.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43570 (s : N.State) (i : N.Inputs) :
  R.v43570 (state s) (inputs i) = Zmod.unsigned (N.v43570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43570 s i)) at 1.
  unfold R.v43570, N.v43570.
  unfold R.v6, N.v6.
  rewrite ?node_11210.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43571 (s : N.State) (i : N.Inputs) :
  R.v43571 (state s) (inputs i) = Zmod.unsigned (N.v43571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43571 s i)) at 1.
  unfold R.v43571, N.v43571.
  rewrite ?node_43568.
  rewrite ?node_43569.
  rewrite ?node_43570.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43572 (s : N.State) (i : N.Inputs) :
  R.v43572 (state s) (inputs i) = Zmod.unsigned (N.v43572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43572 s i)) at 1.
  unfold R.v43572, N.v43572.
  rewrite ?node_43567.
  rewrite ?node_43571.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43573 (s : N.State) (i : N.Inputs) :
  R.v43573 (state s) (inputs i) = Zmod.unsigned (N.v43573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43573 s i)) at 1.
  unfold R.v43573, N.v43573.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43574 (s : N.State) (i : N.Inputs) :
  R.v43574 (state s) (inputs i) = Zmod.unsigned (N.v43574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43574 s i)) at 1.
  unfold R.v43574, N.v43574.
  rewrite ?node_11018.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43575 (s : N.State) (i : N.Inputs) :
  R.v43575 (state s) (inputs i) = Zmod.unsigned (N.v43575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43575 s i)) at 1.
  unfold R.v43575, N.v43575.
  unfold R.v6, N.v6.
  rewrite ?node_11014.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43576 (s : N.State) (i : N.Inputs) :
  R.v43576 (state s) (inputs i) = Zmod.unsigned (N.v43576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43576 s i)) at 1.
  unfold R.v43576, N.v43576.
  unfold R.v6, N.v6.
  rewrite ?node_11011.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43577 (s : N.State) (i : N.Inputs) :
  R.v43577 (state s) (inputs i) = Zmod.unsigned (N.v43577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43577 s i)) at 1.
  unfold R.v43577, N.v43577.
  rewrite ?node_43575.
  rewrite ?node_43576.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43578 (s : N.State) (i : N.Inputs) :
  R.v43578 (state s) (inputs i) = Zmod.unsigned (N.v43578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43578 s i)) at 1.
  unfold R.v43578, N.v43578.
  unfold R.v16484, N.v16484.
  rewrite ?node_43577.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43579 (s : N.State) (i : N.Inputs) :
  R.v43579 (state s) (inputs i) = Zmod.unsigned (N.v43579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43579 s i)) at 1.
  unfold R.v43579, N.v43579.
  rewrite ?node_43574.
  rewrite ?node_43578.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43580 (s : N.State) (i : N.Inputs) :
  R.v43580 (state s) (inputs i) = Zmod.unsigned (N.v43580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43580 s i)) at 1.
  unfold R.v43580, N.v43580.
  unfold R.v6, N.v6.
  rewrite ?node_43579.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43581 (s : N.State) (i : N.Inputs) :
  R.v43581 (state s) (inputs i) = Zmod.unsigned (N.v43581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43581 s i)) at 1.
  unfold R.v43581, N.v43581.
  rewrite ?node_11019.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43582 (s : N.State) (i : N.Inputs) :
  R.v43582 (state s) (inputs i) = Zmod.unsigned (N.v43582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43582 s i)) at 1.
  unfold R.v43582, N.v43582.
  unfold R.v6, N.v6.
  rewrite ?node_11190.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43583 (s : N.State) (i : N.Inputs) :
  R.v43583 (state s) (inputs i) = Zmod.unsigned (N.v43583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43583 s i)) at 1.
  unfold R.v43583, N.v43583.
  rewrite ?node_43581.
  rewrite ?node_43582.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43584 (s : N.State) (i : N.Inputs) :
  R.v43584 (state s) (inputs i) = Zmod.unsigned (N.v43584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43584 s i)) at 1.
  unfold R.v43584, N.v43584.
  rewrite ?node_43580.
  rewrite ?node_43583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43585 (s : N.State) (i : N.Inputs) :
  R.v43585 (state s) (inputs i) = Zmod.unsigned (N.v43585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43585 s i)) at 1.
  unfold R.v43585, N.v43585.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43586 (s : N.State) (i : N.Inputs) :
  R.v43586 (state s) (inputs i) = Zmod.unsigned (N.v43586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43586 s i)) at 1.
  unfold R.v43586, N.v43586.
  rewrite ?node_11026.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43587 (s : N.State) (i : N.Inputs) :
  R.v43587 (state s) (inputs i) = Zmod.unsigned (N.v43587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43587 s i)) at 1.
  unfold R.v43587, N.v43587.
  unfold R.v6, N.v6.
  rewrite ?node_11022.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43588 (s : N.State) (i : N.Inputs) :
  R.v43588 (state s) (inputs i) = Zmod.unsigned (N.v43588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43588 s i)) at 1.
  unfold R.v43588, N.v43588.
  unfold R.v6, N.v6.
  rewrite ?node_11019.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43589 (s : N.State) (i : N.Inputs) :
  R.v43589 (state s) (inputs i) = Zmod.unsigned (N.v43589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43589 s i)) at 1.
  unfold R.v43589, N.v43589.
  rewrite ?node_43587.
  rewrite ?node_43588.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43590 (s : N.State) (i : N.Inputs) :
  R.v43590 (state s) (inputs i) = Zmod.unsigned (N.v43590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43590 s i)) at 1.
  unfold R.v43590, N.v43590.
  unfold R.v16484, N.v16484.
  rewrite ?node_43589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43591 (s : N.State) (i : N.Inputs) :
  R.v43591 (state s) (inputs i) = Zmod.unsigned (N.v43591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43591 s i)) at 1.
  unfold R.v43591, N.v43591.
  rewrite ?node_43586.
  rewrite ?node_43590.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43592 (s : N.State) (i : N.Inputs) :
  R.v43592 (state s) (inputs i) = Zmod.unsigned (N.v43592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43592 s i)) at 1.
  unfold R.v43592, N.v43592.
  unfold R.v6, N.v6.
  rewrite ?node_43591.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43593 (s : N.State) (i : N.Inputs) :
  R.v43593 (state s) (inputs i) = Zmod.unsigned (N.v43593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43593 s i)) at 1.
  unfold R.v43593, N.v43593.
  rewrite ?node_11027.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43594 (s : N.State) (i : N.Inputs) :
  R.v43594 (state s) (inputs i) = Zmod.unsigned (N.v43594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43594 s i)) at 1.
  unfold R.v43594, N.v43594.
  unfold R.v6, N.v6.
  rewrite ?node_11210.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43595 (s : N.State) (i : N.Inputs) :
  R.v43595 (state s) (inputs i) = Zmod.unsigned (N.v43595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43595 s i)) at 1.
  unfold R.v43595, N.v43595.
  rewrite ?node_43593.
  rewrite ?node_43594.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43596 (s : N.State) (i : N.Inputs) :
  R.v43596 (state s) (inputs i) = Zmod.unsigned (N.v43596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43596 s i)) at 1.
  unfold R.v43596, N.v43596.
  rewrite ?node_43592.
  rewrite ?node_43595.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43597 (s : N.State) (i : N.Inputs) :
  R.v43597 (state s) (inputs i) = Zmod.unsigned (N.v43597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43597 s i)) at 1.
  unfold R.v43597, N.v43597.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43598 (s : N.State) (i : N.Inputs) :
  R.v43598 (state s) (inputs i) = Zmod.unsigned (N.v43598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43598 s i)) at 1.
  unfold R.v43598, N.v43598.
  rewrite ?node_11115.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43599 (s : N.State) (i : N.Inputs) :
  R.v43599 (state s) (inputs i) = Zmod.unsigned (N.v43599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43599 s i)) at 1.
  unfold R.v43599, N.v43599.
  rewrite ?node_11111.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43600 (s : N.State) (i : N.Inputs) :
  R.v43600 (state s) (inputs i) = Zmod.unsigned (N.v43600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43600 s i)) at 1.
  unfold R.v43600, N.v43600.
  rewrite ?node_11103.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43601 (s : N.State) (i : N.Inputs) :
  R.v43601 (state s) (inputs i) = Zmod.unsigned (N.v43601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43601 s i)) at 1.
  unfold R.v43601, N.v43601.
  unfold R.v6, N.v6.
  rewrite ?node_11095.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43602 (s : N.State) (i : N.Inputs) :
  R.v43602 (state s) (inputs i) = Zmod.unsigned (N.v43602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43602 s i)) at 1.
  unfold R.v43602, N.v43602.
  unfold R.v6, N.v6.
  rewrite ?node_11088.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43603 (s : N.State) (i : N.Inputs) :
  R.v43603 (state s) (inputs i) = Zmod.unsigned (N.v43603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43603 s i)) at 1.
  unfold R.v43603, N.v43603.
  rewrite ?node_43601.
  rewrite ?node_43602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43604 (s : N.State) (i : N.Inputs) :
  R.v43604 (state s) (inputs i) = Zmod.unsigned (N.v43604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43604 s i)) at 1.
  unfold R.v43604, N.v43604.
  unfold R.v16484, N.v16484.
  rewrite ?node_43603.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43605 (s : N.State) (i : N.Inputs) :
  R.v43605 (state s) (inputs i) = Zmod.unsigned (N.v43605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43605 s i)) at 1.
  unfold R.v43605, N.v43605.
  rewrite ?node_43598.
  rewrite ?node_43599.
  rewrite ?node_43600.
  rewrite ?node_43604.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43606 (s : N.State) (i : N.Inputs) :
  R.v43606 (state s) (inputs i) = Zmod.unsigned (N.v43606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43606 s i)) at 1.
  unfold R.v43606, N.v43606.
  unfold R.v6, N.v6.
  rewrite ?node_43605.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43607 (s : N.State) (i : N.Inputs) :
  R.v43607 (state s) (inputs i) = Zmod.unsigned (N.v43607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43607 s i)) at 1.
  unfold R.v43607, N.v43607.
  rewrite ?node_11116.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43608 (s : N.State) (i : N.Inputs) :
  R.v43608 (state s) (inputs i) = Zmod.unsigned (N.v43608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43608 s i)) at 1.
  unfold R.v43608, N.v43608.
  unfold R.v6, N.v6.
  rewrite ?node_11274.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43609 (s : N.State) (i : N.Inputs) :
  R.v43609 (state s) (inputs i) = Zmod.unsigned (N.v43609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43609 s i)) at 1.
  unfold R.v43609, N.v43609.
  unfold R.v6, N.v6.
  rewrite ?node_11356.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43610 (s : N.State) (i : N.Inputs) :
  R.v43610 (state s) (inputs i) = Zmod.unsigned (N.v43610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43610 s i)) at 1.
  unfold R.v43610, N.v43610.
  rewrite ?node_43607.
  rewrite ?node_43608.
  rewrite ?node_43609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43611 (s : N.State) (i : N.Inputs) :
  R.v43611 (state s) (inputs i) = Zmod.unsigned (N.v43611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43611 s i)) at 1.
  unfold R.v43611, N.v43611.
  rewrite ?node_43606.
  rewrite ?node_43610.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43612 (s : N.State) (i : N.Inputs) :
  R.v43612 (state s) (inputs i) = Zmod.unsigned (N.v43612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43612 s i)) at 1.
  unfold R.v43612, N.v43612.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43613 (s : N.State) (i : N.Inputs) :
  R.v43613 (state s) (inputs i) = Zmod.unsigned (N.v43613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43613 s i)) at 1.
  unfold R.v43613, N.v43613.
  rewrite ?node_11103.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43614 (s : N.State) (i : N.Inputs) :
  R.v43614 (state s) (inputs i) = Zmod.unsigned (N.v43614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43614 s i)) at 1.
  unfold R.v43614, N.v43614.
  unfold R.v6, N.v6.
  rewrite ?node_11095.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43615 (s : N.State) (i : N.Inputs) :
  R.v43615 (state s) (inputs i) = Zmod.unsigned (N.v43615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43615 s i)) at 1.
  unfold R.v43615, N.v43615.
  unfold R.v6, N.v6.
  rewrite ?node_11088.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43616 (s : N.State) (i : N.Inputs) :
  R.v43616 (state s) (inputs i) = Zmod.unsigned (N.v43616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43616 s i)) at 1.
  unfold R.v43616, N.v43616.
  rewrite ?node_43614.
  rewrite ?node_43615.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43617 (s : N.State) (i : N.Inputs) :
  R.v43617 (state s) (inputs i) = Zmod.unsigned (N.v43617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43617 s i)) at 1.
  unfold R.v43617, N.v43617.
  unfold R.v16484, N.v16484.
  rewrite ?node_43616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43618 (s : N.State) (i : N.Inputs) :
  R.v43618 (state s) (inputs i) = Zmod.unsigned (N.v43618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43618 s i)) at 1.
  unfold R.v43618, N.v43618.
  rewrite ?node_43613.
  rewrite ?node_43617.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43619 (s : N.State) (i : N.Inputs) :
  R.v43619 (state s) (inputs i) = Zmod.unsigned (N.v43619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43619 s i)) at 1.
  unfold R.v43619, N.v43619.
  unfold R.v6, N.v6.
  rewrite ?node_43618.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43620 (s : N.State) (i : N.Inputs) :
  R.v43620 (state s) (inputs i) = Zmod.unsigned (N.v43620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43620 s i)) at 1.
  unfold R.v43620, N.v43620.
  rewrite ?node_11104.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43621 (s : N.State) (i : N.Inputs) :
  R.v43621 (state s) (inputs i) = Zmod.unsigned (N.v43621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43621 s i)) at 1.
  unfold R.v43621, N.v43621.
  unfold R.v6, N.v6.
  rewrite ?node_11274.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43622 (s : N.State) (i : N.Inputs) :
  R.v43622 (state s) (inputs i) = Zmod.unsigned (N.v43622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43622 s i)) at 1.
  unfold R.v43622, N.v43622.
  rewrite ?node_43620.
  rewrite ?node_43621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43623 (s : N.State) (i : N.Inputs) :
  R.v43623 (state s) (inputs i) = Zmod.unsigned (N.v43623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43623 s i)) at 1.
  unfold R.v43623, N.v43623.
  rewrite ?node_43619.
  rewrite ?node_43622.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43624 (s : N.State) (i : N.Inputs) :
  R.v43624 (state s) (inputs i) = Zmod.unsigned (N.v43624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43624 s i)) at 1.
  unfold R.v43624, N.v43624.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43625 (s : N.State) (i : N.Inputs) :
  R.v43625 (state s) (inputs i) = Zmod.unsigned (N.v43625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43625 s i)) at 1.
  unfold R.v43625, N.v43625.
  rewrite ?node_11115.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43626 (s : N.State) (i : N.Inputs) :
  R.v43626 (state s) (inputs i) = Zmod.unsigned (N.v43626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43626 s i)) at 1.
  unfold R.v43626, N.v43626.
  unfold R.v6, N.v6.
  rewrite ?node_11111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43627 (s : N.State) (i : N.Inputs) :
  R.v43627 (state s) (inputs i) = Zmod.unsigned (N.v43627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43627 s i)) at 1.
  unfold R.v43627, N.v43627.
  unfold R.v6, N.v6.
  rewrite ?node_11104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43628 (s : N.State) (i : N.Inputs) :
  R.v43628 (state s) (inputs i) = Zmod.unsigned (N.v43628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43628 s i)) at 1.
  unfold R.v43628, N.v43628.
  rewrite ?node_43626.
  rewrite ?node_43627.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43629 (s : N.State) (i : N.Inputs) :
  R.v43629 (state s) (inputs i) = Zmod.unsigned (N.v43629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43629 s i)) at 1.
  unfold R.v43629, N.v43629.
  unfold R.v16484, N.v16484.
  rewrite ?node_43628.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43630 (s : N.State) (i : N.Inputs) :
  R.v43630 (state s) (inputs i) = Zmod.unsigned (N.v43630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43630 s i)) at 1.
  unfold R.v43630, N.v43630.
  rewrite ?node_43625.
  rewrite ?node_43629.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43631 (s : N.State) (i : N.Inputs) :
  R.v43631 (state s) (inputs i) = Zmod.unsigned (N.v43631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43631 s i)) at 1.
  unfold R.v43631, N.v43631.
  unfold R.v6, N.v6.
  rewrite ?node_43630.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43632 (s : N.State) (i : N.Inputs) :
  R.v43632 (state s) (inputs i) = Zmod.unsigned (N.v43632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43632 s i)) at 1.
  unfold R.v43632, N.v43632.
  rewrite ?node_11116.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43633 (s : N.State) (i : N.Inputs) :
  R.v43633 (state s) (inputs i) = Zmod.unsigned (N.v43633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43633 s i)) at 1.
  unfold R.v43633, N.v43633.
  unfold R.v6, N.v6.
  rewrite ?node_11356.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43634 (s : N.State) (i : N.Inputs) :
  R.v43634 (state s) (inputs i) = Zmod.unsigned (N.v43634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43634 s i)) at 1.
  unfold R.v43634, N.v43634.
  rewrite ?node_43632.
  rewrite ?node_43633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43635 (s : N.State) (i : N.Inputs) :
  R.v43635 (state s) (inputs i) = Zmod.unsigned (N.v43635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43635 s i)) at 1.
  unfold R.v43635, N.v43635.
  rewrite ?node_43631.
  rewrite ?node_43634.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43636 (s : N.State) (i : N.Inputs) :
  R.v43636 (state s) (inputs i) = Zmod.unsigned (N.v43636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43636 s i)) at 1.
  unfold R.v43636, N.v43636.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43637 (s : N.State) (i : N.Inputs) :
  R.v43637 (state s) (inputs i) = Zmod.unsigned (N.v43637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43637 s i)) at 1.
  unfold R.v43637, N.v43637.
  rewrite ?node_11150.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43638 (s : N.State) (i : N.Inputs) :
  R.v43638 (state s) (inputs i) = Zmod.unsigned (N.v43638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43638 s i)) at 1.
  unfold R.v43638, N.v43638.
  rewrite ?node_11146.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43639 (s : N.State) (i : N.Inputs) :
  R.v43639 (state s) (inputs i) = Zmod.unsigned (N.v43639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43639 s i)) at 1.
  unfold R.v43639, N.v43639.
  rewrite ?node_11138.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43640 (s : N.State) (i : N.Inputs) :
  R.v43640 (state s) (inputs i) = Zmod.unsigned (N.v43640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43640 s i)) at 1.
  unfold R.v43640, N.v43640.
  unfold R.v6, N.v6.
  rewrite ?node_11130.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43641 (s : N.State) (i : N.Inputs) :
  R.v43641 (state s) (inputs i) = Zmod.unsigned (N.v43641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43641 s i)) at 1.
  unfold R.v43641, N.v43641.
  unfold R.v6, N.v6.
  rewrite ?node_11123.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43642 (s : N.State) (i : N.Inputs) :
  R.v43642 (state s) (inputs i) = Zmod.unsigned (N.v43642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43642 s i)) at 1.
  unfold R.v43642, N.v43642.
  rewrite ?node_43640.
  rewrite ?node_43641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43643 (s : N.State) (i : N.Inputs) :
  R.v43643 (state s) (inputs i) = Zmod.unsigned (N.v43643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43643 s i)) at 1.
  unfold R.v43643, N.v43643.
  unfold R.v16484, N.v16484.
  rewrite ?node_43642.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43644 (s : N.State) (i : N.Inputs) :
  R.v43644 (state s) (inputs i) = Zmod.unsigned (N.v43644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43644 s i)) at 1.
  unfold R.v43644, N.v43644.
  rewrite ?node_43637.
  rewrite ?node_43638.
  rewrite ?node_43639.
  rewrite ?node_43643.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43645 (s : N.State) (i : N.Inputs) :
  R.v43645 (state s) (inputs i) = Zmod.unsigned (N.v43645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43645 s i)) at 1.
  unfold R.v43645, N.v43645.
  unfold R.v6, N.v6.
  rewrite ?node_43644.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43646 (s : N.State) (i : N.Inputs) :
  R.v43646 (state s) (inputs i) = Zmod.unsigned (N.v43646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43646 s i)) at 1.
  unfold R.v43646, N.v43646.
  rewrite ?node_11151.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43647 (s : N.State) (i : N.Inputs) :
  R.v43647 (state s) (inputs i) = Zmod.unsigned (N.v43647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43647 s i)) at 1.
  unfold R.v43647, N.v43647.
  unfold R.v6, N.v6.
  rewrite ?node_11304.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43648 (s : N.State) (i : N.Inputs) :
  R.v43648 (state s) (inputs i) = Zmod.unsigned (N.v43648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43648 s i)) at 1.
  unfold R.v43648, N.v43648.
  unfold R.v6, N.v6.
  rewrite ?node_11360.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43649 (s : N.State) (i : N.Inputs) :
  R.v43649 (state s) (inputs i) = Zmod.unsigned (N.v43649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43649 s i)) at 1.
  unfold R.v43649, N.v43649.
  rewrite ?node_43646.
  rewrite ?node_43647.
  rewrite ?node_43648.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43650 (s : N.State) (i : N.Inputs) :
  R.v43650 (state s) (inputs i) = Zmod.unsigned (N.v43650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43650 s i)) at 1.
  unfold R.v43650, N.v43650.
  rewrite ?node_43645.
  rewrite ?node_43649.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43651 (s : N.State) (i : N.Inputs) :
  R.v43651 (state s) (inputs i) = Zmod.unsigned (N.v43651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43651 s i)) at 1.
  unfold R.v43651, N.v43651.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43652 (s : N.State) (i : N.Inputs) :
  R.v43652 (state s) (inputs i) = Zmod.unsigned (N.v43652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43652 s i)) at 1.
  unfold R.v43652, N.v43652.
  rewrite ?node_11138.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43653 (s : N.State) (i : N.Inputs) :
  R.v43653 (state s) (inputs i) = Zmod.unsigned (N.v43653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43653 s i)) at 1.
  unfold R.v43653, N.v43653.
  unfold R.v6, N.v6.
  rewrite ?node_11130.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43654 (s : N.State) (i : N.Inputs) :
  R.v43654 (state s) (inputs i) = Zmod.unsigned (N.v43654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43654 s i)) at 1.
  unfold R.v43654, N.v43654.
  unfold R.v6, N.v6.
  rewrite ?node_11123.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43655 (s : N.State) (i : N.Inputs) :
  R.v43655 (state s) (inputs i) = Zmod.unsigned (N.v43655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43655 s i)) at 1.
  unfold R.v43655, N.v43655.
  rewrite ?node_43653.
  rewrite ?node_43654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43656 (s : N.State) (i : N.Inputs) :
  R.v43656 (state s) (inputs i) = Zmod.unsigned (N.v43656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43656 s i)) at 1.
  unfold R.v43656, N.v43656.
  unfold R.v16484, N.v16484.
  rewrite ?node_43655.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43657 (s : N.State) (i : N.Inputs) :
  R.v43657 (state s) (inputs i) = Zmod.unsigned (N.v43657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43657 s i)) at 1.
  unfold R.v43657, N.v43657.
  rewrite ?node_43652.
  rewrite ?node_43656.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43658 (s : N.State) (i : N.Inputs) :
  R.v43658 (state s) (inputs i) = Zmod.unsigned (N.v43658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43658 s i)) at 1.
  unfold R.v43658, N.v43658.
  unfold R.v6, N.v6.
  rewrite ?node_43657.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43659 (s : N.State) (i : N.Inputs) :
  R.v43659 (state s) (inputs i) = Zmod.unsigned (N.v43659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43659 s i)) at 1.
  unfold R.v43659, N.v43659.
  rewrite ?node_11139.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43660 (s : N.State) (i : N.Inputs) :
  R.v43660 (state s) (inputs i) = Zmod.unsigned (N.v43660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43660 s i)) at 1.
  unfold R.v43660, N.v43660.
  unfold R.v6, N.v6.
  rewrite ?node_11304.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43661 (s : N.State) (i : N.Inputs) :
  R.v43661 (state s) (inputs i) = Zmod.unsigned (N.v43661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43661 s i)) at 1.
  unfold R.v43661, N.v43661.
  rewrite ?node_43659.
  rewrite ?node_43660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43662 (s : N.State) (i : N.Inputs) :
  R.v43662 (state s) (inputs i) = Zmod.unsigned (N.v43662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43662 s i)) at 1.
  unfold R.v43662, N.v43662.
  rewrite ?node_43658.
  rewrite ?node_43661.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43663 (s : N.State) (i : N.Inputs) :
  R.v43663 (state s) (inputs i) = Zmod.unsigned (N.v43663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43663 s i)) at 1.
  unfold R.v43663, N.v43663.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43664 (s : N.State) (i : N.Inputs) :
  R.v43664 (state s) (inputs i) = Zmod.unsigned (N.v43664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43664 s i)) at 1.
  unfold R.v43664, N.v43664.
  rewrite ?node_11150.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43665 (s : N.State) (i : N.Inputs) :
  R.v43665 (state s) (inputs i) = Zmod.unsigned (N.v43665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43665 s i)) at 1.
  unfold R.v43665, N.v43665.
  unfold R.v6, N.v6.
  rewrite ?node_11146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43666 (s : N.State) (i : N.Inputs) :
  R.v43666 (state s) (inputs i) = Zmod.unsigned (N.v43666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43666 s i)) at 1.
  unfold R.v43666, N.v43666.
  unfold R.v6, N.v6.
  rewrite ?node_11139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43667 (s : N.State) (i : N.Inputs) :
  R.v43667 (state s) (inputs i) = Zmod.unsigned (N.v43667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43667 s i)) at 1.
  unfold R.v43667, N.v43667.
  rewrite ?node_43665.
  rewrite ?node_43666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43668 (s : N.State) (i : N.Inputs) :
  R.v43668 (state s) (inputs i) = Zmod.unsigned (N.v43668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43668 s i)) at 1.
  unfold R.v43668, N.v43668.
  unfold R.v16484, N.v16484.
  rewrite ?node_43667.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43669 (s : N.State) (i : N.Inputs) :
  R.v43669 (state s) (inputs i) = Zmod.unsigned (N.v43669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43669 s i)) at 1.
  unfold R.v43669, N.v43669.
  rewrite ?node_43664.
  rewrite ?node_43668.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43670 (s : N.State) (i : N.Inputs) :
  R.v43670 (state s) (inputs i) = Zmod.unsigned (N.v43670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43670 s i)) at 1.
  unfold R.v43670, N.v43670.
  unfold R.v6, N.v6.
  rewrite ?node_43669.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43671 (s : N.State) (i : N.Inputs) :
  R.v43671 (state s) (inputs i) = Zmod.unsigned (N.v43671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43671 s i)) at 1.
  unfold R.v43671, N.v43671.
  rewrite ?node_11151.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43672 (s : N.State) (i : N.Inputs) :
  R.v43672 (state s) (inputs i) = Zmod.unsigned (N.v43672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43672 s i)) at 1.
  unfold R.v43672, N.v43672.
  unfold R.v6, N.v6.
  rewrite ?node_11360.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43673 (s : N.State) (i : N.Inputs) :
  R.v43673 (state s) (inputs i) = Zmod.unsigned (N.v43673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43673 s i)) at 1.
  unfold R.v43673, N.v43673.
  rewrite ?node_43671.
  rewrite ?node_43672.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43674 (s : N.State) (i : N.Inputs) :
  R.v43674 (state s) (inputs i) = Zmod.unsigned (N.v43674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43674 s i)) at 1.
  unfold R.v43674, N.v43674.
  rewrite ?node_43670.
  rewrite ?node_43673.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43675 (s : N.State) (i : N.Inputs) :
  R.v43675 (state s) (inputs i) = Zmod.unsigned (N.v43675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43675 s i)) at 1.
  unfold R.v43675, N.v43675.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43676 (s : N.State) (i : N.Inputs) :
  R.v43676 (state s) (inputs i) = Zmod.unsigned (N.v43676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43676 s i)) at 1.
  unfold R.v43676, N.v43676.
  rewrite ?node_11170.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43677 (s : N.State) (i : N.Inputs) :
  R.v43677 (state s) (inputs i) = Zmod.unsigned (N.v43677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43677 s i)) at 1.
  unfold R.v43677, N.v43677.
  rewrite ?node_11166.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43678 (s : N.State) (i : N.Inputs) :
  R.v43678 (state s) (inputs i) = Zmod.unsigned (N.v43678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43678 s i)) at 1.
  unfold R.v43678, N.v43678.
  rewrite ?node_11162.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43679 (s : N.State) (i : N.Inputs) :
  R.v43679 (state s) (inputs i) = Zmod.unsigned (N.v43679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43679 s i)) at 1.
  unfold R.v43679, N.v43679.
  unfold R.v6, N.v6.
  rewrite ?node_11158.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43680 (s : N.State) (i : N.Inputs) :
  R.v43680 (state s) (inputs i) = Zmod.unsigned (N.v43680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43680 s i)) at 1.
  unfold R.v43680, N.v43680.
  unfold R.v6, N.v6.
  rewrite ?node_11155.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43681 (s : N.State) (i : N.Inputs) :
  R.v43681 (state s) (inputs i) = Zmod.unsigned (N.v43681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43681 s i)) at 1.
  unfold R.v43681, N.v43681.
  rewrite ?node_43679.
  rewrite ?node_43680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43682 (s : N.State) (i : N.Inputs) :
  R.v43682 (state s) (inputs i) = Zmod.unsigned (N.v43682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43682 s i)) at 1.
  unfold R.v43682, N.v43682.
  unfold R.v16484, N.v16484.
  rewrite ?node_43681.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43683 (s : N.State) (i : N.Inputs) :
  R.v43683 (state s) (inputs i) = Zmod.unsigned (N.v43683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43683 s i)) at 1.
  unfold R.v43683, N.v43683.
  rewrite ?node_43676.
  rewrite ?node_43677.
  rewrite ?node_43678.
  rewrite ?node_43682.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43684 (s : N.State) (i : N.Inputs) :
  R.v43684 (state s) (inputs i) = Zmod.unsigned (N.v43684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43684 s i)) at 1.
  unfold R.v43684, N.v43684.
  unfold R.v6, N.v6.
  rewrite ?node_43683.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43685 (s : N.State) (i : N.Inputs) :
  R.v43685 (state s) (inputs i) = Zmod.unsigned (N.v43685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43685 s i)) at 1.
  unfold R.v43685, N.v43685.
  rewrite ?node_11171.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43686 (s : N.State) (i : N.Inputs) :
  R.v43686 (state s) (inputs i) = Zmod.unsigned (N.v43686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43686 s i)) at 1.
  unfold R.v43686, N.v43686.
  unfold R.v6, N.v6.
  rewrite ?node_11324.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43687 (s : N.State) (i : N.Inputs) :
  R.v43687 (state s) (inputs i) = Zmod.unsigned (N.v43687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43687 s i)) at 1.
  unfold R.v43687, N.v43687.
  unfold R.v6, N.v6.
  rewrite ?node_11364.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43688 (s : N.State) (i : N.Inputs) :
  R.v43688 (state s) (inputs i) = Zmod.unsigned (N.v43688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43688 s i)) at 1.
  unfold R.v43688, N.v43688.
  rewrite ?node_43685.
  rewrite ?node_43686.
  rewrite ?node_43687.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43689 (s : N.State) (i : N.Inputs) :
  R.v43689 (state s) (inputs i) = Zmod.unsigned (N.v43689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43689 s i)) at 1.
  unfold R.v43689, N.v43689.
  rewrite ?node_43684.
  rewrite ?node_43688.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43690 (s : N.State) (i : N.Inputs) :
  R.v43690 (state s) (inputs i) = Zmod.unsigned (N.v43690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43690 s i)) at 1.
  unfold R.v43690, N.v43690.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43691 (s : N.State) (i : N.Inputs) :
  R.v43691 (state s) (inputs i) = Zmod.unsigned (N.v43691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43691 s i)) at 1.
  unfold R.v43691, N.v43691.
  rewrite ?node_11162.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43692 (s : N.State) (i : N.Inputs) :
  R.v43692 (state s) (inputs i) = Zmod.unsigned (N.v43692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43692 s i)) at 1.
  unfold R.v43692, N.v43692.
  unfold R.v6, N.v6.
  rewrite ?node_11158.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43693 (s : N.State) (i : N.Inputs) :
  R.v43693 (state s) (inputs i) = Zmod.unsigned (N.v43693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43693 s i)) at 1.
  unfold R.v43693, N.v43693.
  unfold R.v6, N.v6.
  rewrite ?node_11155.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43694 (s : N.State) (i : N.Inputs) :
  R.v43694 (state s) (inputs i) = Zmod.unsigned (N.v43694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43694 s i)) at 1.
  unfold R.v43694, N.v43694.
  rewrite ?node_43692.
  rewrite ?node_43693.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43695 (s : N.State) (i : N.Inputs) :
  R.v43695 (state s) (inputs i) = Zmod.unsigned (N.v43695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43695 s i)) at 1.
  unfold R.v43695, N.v43695.
  unfold R.v16484, N.v16484.
  rewrite ?node_43694.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43696 (s : N.State) (i : N.Inputs) :
  R.v43696 (state s) (inputs i) = Zmod.unsigned (N.v43696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43696 s i)) at 1.
  unfold R.v43696, N.v43696.
  rewrite ?node_43691.
  rewrite ?node_43695.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43697 (s : N.State) (i : N.Inputs) :
  R.v43697 (state s) (inputs i) = Zmod.unsigned (N.v43697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43697 s i)) at 1.
  unfold R.v43697, N.v43697.
  unfold R.v6, N.v6.
  rewrite ?node_43696.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43698 (s : N.State) (i : N.Inputs) :
  R.v43698 (state s) (inputs i) = Zmod.unsigned (N.v43698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43698 s i)) at 1.
  unfold R.v43698, N.v43698.
  rewrite ?node_11163.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43699 (s : N.State) (i : N.Inputs) :
  R.v43699 (state s) (inputs i) = Zmod.unsigned (N.v43699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43699 s i)) at 1.
  unfold R.v43699, N.v43699.
  unfold R.v6, N.v6.
  rewrite ?node_11324.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43700 (s : N.State) (i : N.Inputs) :
  R.v43700 (state s) (inputs i) = Zmod.unsigned (N.v43700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43700 s i)) at 1.
  unfold R.v43700, N.v43700.
  rewrite ?node_43698.
  rewrite ?node_43699.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43701 (s : N.State) (i : N.Inputs) :
  R.v43701 (state s) (inputs i) = Zmod.unsigned (N.v43701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43701 s i)) at 1.
  unfold R.v43701, N.v43701.
  rewrite ?node_43697.
  rewrite ?node_43700.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43702 (s : N.State) (i : N.Inputs) :
  R.v43702 (state s) (inputs i) = Zmod.unsigned (N.v43702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43702 s i)) at 1.
  unfold R.v43702, N.v43702.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43703 (s : N.State) (i : N.Inputs) :
  R.v43703 (state s) (inputs i) = Zmod.unsigned (N.v43703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43703 s i)) at 1.
  unfold R.v43703, N.v43703.
  rewrite ?node_11170.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43704 (s : N.State) (i : N.Inputs) :
  R.v43704 (state s) (inputs i) = Zmod.unsigned (N.v43704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43704 s i)) at 1.
  unfold R.v43704, N.v43704.
  unfold R.v6, N.v6.
  rewrite ?node_11166.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43705 (s : N.State) (i : N.Inputs) :
  R.v43705 (state s) (inputs i) = Zmod.unsigned (N.v43705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43705 s i)) at 1.
  unfold R.v43705, N.v43705.
  unfold R.v6, N.v6.
  rewrite ?node_11163.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43706 (s : N.State) (i : N.Inputs) :
  R.v43706 (state s) (inputs i) = Zmod.unsigned (N.v43706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43706 s i)) at 1.
  unfold R.v43706, N.v43706.
  rewrite ?node_43704.
  rewrite ?node_43705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43707 (s : N.State) (i : N.Inputs) :
  R.v43707 (state s) (inputs i) = Zmod.unsigned (N.v43707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43707 s i)) at 1.
  unfold R.v43707, N.v43707.
  unfold R.v16484, N.v16484.
  rewrite ?node_43706.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43708 (s : N.State) (i : N.Inputs) :
  R.v43708 (state s) (inputs i) = Zmod.unsigned (N.v43708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43708 s i)) at 1.
  unfold R.v43708, N.v43708.
  rewrite ?node_43703.
  rewrite ?node_43707.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43709 (s : N.State) (i : N.Inputs) :
  R.v43709 (state s) (inputs i) = Zmod.unsigned (N.v43709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43709 s i)) at 1.
  unfold R.v43709, N.v43709.
  unfold R.v6, N.v6.
  rewrite ?node_43708.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43710 (s : N.State) (i : N.Inputs) :
  R.v43710 (state s) (inputs i) = Zmod.unsigned (N.v43710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43710 s i)) at 1.
  unfold R.v43710, N.v43710.
  rewrite ?node_11171.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43711 (s : N.State) (i : N.Inputs) :
  R.v43711 (state s) (inputs i) = Zmod.unsigned (N.v43711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43711 s i)) at 1.
  unfold R.v43711, N.v43711.
  unfold R.v6, N.v6.
  rewrite ?node_11364.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43712 (s : N.State) (i : N.Inputs) :
  R.v43712 (state s) (inputs i) = Zmod.unsigned (N.v43712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43712 s i)) at 1.
  unfold R.v43712, N.v43712.
  rewrite ?node_43710.
  rewrite ?node_43711.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43713 (s : N.State) (i : N.Inputs) :
  R.v43713 (state s) (inputs i) = Zmod.unsigned (N.v43713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43713 s i)) at 1.
  unfold R.v43713, N.v43713.
  rewrite ?node_43709.
  rewrite ?node_43712.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43714 (s : N.State) (i : N.Inputs) :
  R.v43714 (state s) (inputs i) = Zmod.unsigned (N.v43714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43714 s i)) at 1.
  unfold R.v43714, N.v43714.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43715 (s : N.State) (i : N.Inputs) :
  R.v43715 (state s) (inputs i) = Zmod.unsigned (N.v43715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43715 s i)) at 1.
  unfold R.v43715, N.v43715.
  rewrite ?node_11190.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43716 (s : N.State) (i : N.Inputs) :
  R.v43716 (state s) (inputs i) = Zmod.unsigned (N.v43716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43716 s i)) at 1.
  unfold R.v43716, N.v43716.
  rewrite ?node_11186.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43717 (s : N.State) (i : N.Inputs) :
  R.v43717 (state s) (inputs i) = Zmod.unsigned (N.v43717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43717 s i)) at 1.
  unfold R.v43717, N.v43717.
  rewrite ?node_11182.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43718 (s : N.State) (i : N.Inputs) :
  R.v43718 (state s) (inputs i) = Zmod.unsigned (N.v43718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43718 s i)) at 1.
  unfold R.v43718, N.v43718.
  unfold R.v6, N.v6.
  rewrite ?node_11178.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43719 (s : N.State) (i : N.Inputs) :
  R.v43719 (state s) (inputs i) = Zmod.unsigned (N.v43719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43719 s i)) at 1.
  unfold R.v43719, N.v43719.
  unfold R.v6, N.v6.
  rewrite ?node_11175.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43720 (s : N.State) (i : N.Inputs) :
  R.v43720 (state s) (inputs i) = Zmod.unsigned (N.v43720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43720 s i)) at 1.
  unfold R.v43720, N.v43720.
  rewrite ?node_43718.
  rewrite ?node_43719.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43721 (s : N.State) (i : N.Inputs) :
  R.v43721 (state s) (inputs i) = Zmod.unsigned (N.v43721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43721 s i)) at 1.
  unfold R.v43721, N.v43721.
  unfold R.v16484, N.v16484.
  rewrite ?node_43720.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43722 (s : N.State) (i : N.Inputs) :
  R.v43722 (state s) (inputs i) = Zmod.unsigned (N.v43722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43722 s i)) at 1.
  unfold R.v43722, N.v43722.
  rewrite ?node_43715.
  rewrite ?node_43716.
  rewrite ?node_43717.
  rewrite ?node_43721.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43723 (s : N.State) (i : N.Inputs) :
  R.v43723 (state s) (inputs i) = Zmod.unsigned (N.v43723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43723 s i)) at 1.
  unfold R.v43723, N.v43723.
  unfold R.v6, N.v6.
  rewrite ?node_43722.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43724 (s : N.State) (i : N.Inputs) :
  R.v43724 (state s) (inputs i) = Zmod.unsigned (N.v43724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43724 s i)) at 1.
  unfold R.v43724, N.v43724.
  rewrite ?node_11191.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43725 (s : N.State) (i : N.Inputs) :
  R.v43725 (state s) (inputs i) = Zmod.unsigned (N.v43725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43725 s i)) at 1.
  unfold R.v43725, N.v43725.
  unfold R.v6, N.v6.
  rewrite ?node_11344.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43726 (s : N.State) (i : N.Inputs) :
  R.v43726 (state s) (inputs i) = Zmod.unsigned (N.v43726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43726 s i)) at 1.
  unfold R.v43726, N.v43726.
  unfold R.v6, N.v6.
  rewrite ?node_11373.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43727 (s : N.State) (i : N.Inputs) :
  R.v43727 (state s) (inputs i) = Zmod.unsigned (N.v43727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43727 s i)) at 1.
  unfold R.v43727, N.v43727.
  rewrite ?node_43724.
  rewrite ?node_43725.
  rewrite ?node_43726.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43728 (s : N.State) (i : N.Inputs) :
  R.v43728 (state s) (inputs i) = Zmod.unsigned (N.v43728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43728 s i)) at 1.
  unfold R.v43728, N.v43728.
  rewrite ?node_43723.
  rewrite ?node_43727.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43729 (s : N.State) (i : N.Inputs) :
  R.v43729 (state s) (inputs i) = Zmod.unsigned (N.v43729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43729 s i)) at 1.
  unfold R.v43729, N.v43729.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43730 (s : N.State) (i : N.Inputs) :
  R.v43730 (state s) (inputs i) = Zmod.unsigned (N.v43730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43730 s i)) at 1.
  unfold R.v43730, N.v43730.
  rewrite ?node_11182.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43731 (s : N.State) (i : N.Inputs) :
  R.v43731 (state s) (inputs i) = Zmod.unsigned (N.v43731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43731 s i)) at 1.
  unfold R.v43731, N.v43731.
  unfold R.v6, N.v6.
  rewrite ?node_11178.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43732 (s : N.State) (i : N.Inputs) :
  R.v43732 (state s) (inputs i) = Zmod.unsigned (N.v43732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43732 s i)) at 1.
  unfold R.v43732, N.v43732.
  unfold R.v6, N.v6.
  rewrite ?node_11175.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43733 (s : N.State) (i : N.Inputs) :
  R.v43733 (state s) (inputs i) = Zmod.unsigned (N.v43733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43733 s i)) at 1.
  unfold R.v43733, N.v43733.
  rewrite ?node_43731.
  rewrite ?node_43732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43734 (s : N.State) (i : N.Inputs) :
  R.v43734 (state s) (inputs i) = Zmod.unsigned (N.v43734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43734 s i)) at 1.
  unfold R.v43734, N.v43734.
  unfold R.v16484, N.v16484.
  rewrite ?node_43733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43735 (s : N.State) (i : N.Inputs) :
  R.v43735 (state s) (inputs i) = Zmod.unsigned (N.v43735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43735 s i)) at 1.
  unfold R.v43735, N.v43735.
  rewrite ?node_43730.
  rewrite ?node_43734.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43736 (s : N.State) (i : N.Inputs) :
  R.v43736 (state s) (inputs i) = Zmod.unsigned (N.v43736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43736 s i)) at 1.
  unfold R.v43736, N.v43736.
  unfold R.v6, N.v6.
  rewrite ?node_43735.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43737 (s : N.State) (i : N.Inputs) :
  R.v43737 (state s) (inputs i) = Zmod.unsigned (N.v43737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43737 s i)) at 1.
  unfold R.v43737, N.v43737.
  rewrite ?node_11183.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43738 (s : N.State) (i : N.Inputs) :
  R.v43738 (state s) (inputs i) = Zmod.unsigned (N.v43738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43738 s i)) at 1.
  unfold R.v43738, N.v43738.
  unfold R.v6, N.v6.
  rewrite ?node_11344.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43739 (s : N.State) (i : N.Inputs) :
  R.v43739 (state s) (inputs i) = Zmod.unsigned (N.v43739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43739 s i)) at 1.
  unfold R.v43739, N.v43739.
  rewrite ?node_43737.
  rewrite ?node_43738.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43740 (s : N.State) (i : N.Inputs) :
  R.v43740 (state s) (inputs i) = Zmod.unsigned (N.v43740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43740 s i)) at 1.
  unfold R.v43740, N.v43740.
  rewrite ?node_43736.
  rewrite ?node_43739.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43741 (s : N.State) (i : N.Inputs) :
  R.v43741 (state s) (inputs i) = Zmod.unsigned (N.v43741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43741 s i)) at 1.
  unfold R.v43741, N.v43741.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43742 (s : N.State) (i : N.Inputs) :
  R.v43742 (state s) (inputs i) = Zmod.unsigned (N.v43742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43742 s i)) at 1.
  unfold R.v43742, N.v43742.
  rewrite ?node_11190.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43743 (s : N.State) (i : N.Inputs) :
  R.v43743 (state s) (inputs i) = Zmod.unsigned (N.v43743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43743 s i)) at 1.
  unfold R.v43743, N.v43743.
  unfold R.v6, N.v6.
  rewrite ?node_11186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43744 (s : N.State) (i : N.Inputs) :
  R.v43744 (state s) (inputs i) = Zmod.unsigned (N.v43744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43744 s i)) at 1.
  unfold R.v43744, N.v43744.
  unfold R.v6, N.v6.
  rewrite ?node_11183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43745 (s : N.State) (i : N.Inputs) :
  R.v43745 (state s) (inputs i) = Zmod.unsigned (N.v43745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43745 s i)) at 1.
  unfold R.v43745, N.v43745.
  rewrite ?node_43743.
  rewrite ?node_43744.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43746 (s : N.State) (i : N.Inputs) :
  R.v43746 (state s) (inputs i) = Zmod.unsigned (N.v43746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43746 s i)) at 1.
  unfold R.v43746, N.v43746.
  unfold R.v16484, N.v16484.
  rewrite ?node_43745.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43747 (s : N.State) (i : N.Inputs) :
  R.v43747 (state s) (inputs i) = Zmod.unsigned (N.v43747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43747 s i)) at 1.
  unfold R.v43747, N.v43747.
  rewrite ?node_43742.
  rewrite ?node_43746.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43748 (s : N.State) (i : N.Inputs) :
  R.v43748 (state s) (inputs i) = Zmod.unsigned (N.v43748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43748 s i)) at 1.
  unfold R.v43748, N.v43748.
  unfold R.v6, N.v6.
  rewrite ?node_43747.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43749 (s : N.State) (i : N.Inputs) :
  R.v43749 (state s) (inputs i) = Zmod.unsigned (N.v43749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43749 s i)) at 1.
  unfold R.v43749, N.v43749.
  rewrite ?node_11191.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43750 (s : N.State) (i : N.Inputs) :
  R.v43750 (state s) (inputs i) = Zmod.unsigned (N.v43750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43750 s i)) at 1.
  unfold R.v43750, N.v43750.
  unfold R.v6, N.v6.
  rewrite ?node_11373.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43751 (s : N.State) (i : N.Inputs) :
  R.v43751 (state s) (inputs i) = Zmod.unsigned (N.v43751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43751 s i)) at 1.
  unfold R.v43751, N.v43751.
  rewrite ?node_43749.
  rewrite ?node_43750.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43752 (s : N.State) (i : N.Inputs) :
  R.v43752 (state s) (inputs i) = Zmod.unsigned (N.v43752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43752 s i)) at 1.
  unfold R.v43752, N.v43752.
  rewrite ?node_43748.
  rewrite ?node_43751.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43753 (s : N.State) (i : N.Inputs) :
  R.v43753 (state s) (inputs i) = Zmod.unsigned (N.v43753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43753 s i)) at 1.
  unfold R.v43753, N.v43753.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43754 (s : N.State) (i : N.Inputs) :
  R.v43754 (state s) (inputs i) = Zmod.unsigned (N.v43754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43754 s i)) at 1.
  unfold R.v43754, N.v43754.
  rewrite ?node_11274.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43755 (s : N.State) (i : N.Inputs) :
  R.v43755 (state s) (inputs i) = Zmod.unsigned (N.v43755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43755 s i)) at 1.
  unfold R.v43755, N.v43755.
  rewrite ?node_11270.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43756 (s : N.State) (i : N.Inputs) :
  R.v43756 (state s) (inputs i) = Zmod.unsigned (N.v43756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43756 s i)) at 1.
  unfold R.v43756, N.v43756.
  rewrite ?node_11262.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43757 (s : N.State) (i : N.Inputs) :
  R.v43757 (state s) (inputs i) = Zmod.unsigned (N.v43757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43757 s i)) at 1.
  unfold R.v43757, N.v43757.
  unfold R.v6, N.v6.
  rewrite ?node_11254.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43758 (s : N.State) (i : N.Inputs) :
  R.v43758 (state s) (inputs i) = Zmod.unsigned (N.v43758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43758 s i)) at 1.
  unfold R.v43758, N.v43758.
  unfold R.v6, N.v6.
  rewrite ?node_11247.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43759 (s : N.State) (i : N.Inputs) :
  R.v43759 (state s) (inputs i) = Zmod.unsigned (N.v43759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43759 s i)) at 1.
  unfold R.v43759, N.v43759.
  rewrite ?node_43757.
  rewrite ?node_43758.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43760 (s : N.State) (i : N.Inputs) :
  R.v43760 (state s) (inputs i) = Zmod.unsigned (N.v43760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43760 s i)) at 1.
  unfold R.v43760, N.v43760.
  unfold R.v16484, N.v16484.
  rewrite ?node_43759.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43761 (s : N.State) (i : N.Inputs) :
  R.v43761 (state s) (inputs i) = Zmod.unsigned (N.v43761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43761 s i)) at 1.
  unfold R.v43761, N.v43761.
  rewrite ?node_43754.
  rewrite ?node_43755.
  rewrite ?node_43756.
  rewrite ?node_43760.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43762 (s : N.State) (i : N.Inputs) :
  R.v43762 (state s) (inputs i) = Zmod.unsigned (N.v43762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43762 s i)) at 1.
  unfold R.v43762, N.v43762.
  unfold R.v6, N.v6.
  rewrite ?node_43761.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43763 (s : N.State) (i : N.Inputs) :
  R.v43763 (state s) (inputs i) = Zmod.unsigned (N.v43763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43763 s i)) at 1.
  unfold R.v43763, N.v43763.
  rewrite ?node_11275.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43764 (s : N.State) (i : N.Inputs) :
  R.v43764 (state s) (inputs i) = Zmod.unsigned (N.v43764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43764 s i)) at 1.
  unfold R.v43764, N.v43764.
  unfold R.v6, N.v6.
  rewrite ?node_11429.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43765 (s : N.State) (i : N.Inputs) :
  R.v43765 (state s) (inputs i) = Zmod.unsigned (N.v43765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43765 s i)) at 1.
  unfold R.v43765, N.v43765.
  unfold R.v6, N.v6.
  rewrite ?node_11508.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43766 (s : N.State) (i : N.Inputs) :
  R.v43766 (state s) (inputs i) = Zmod.unsigned (N.v43766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43766 s i)) at 1.
  unfold R.v43766, N.v43766.
  rewrite ?node_43763.
  rewrite ?node_43764.
  rewrite ?node_43765.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43767 (s : N.State) (i : N.Inputs) :
  R.v43767 (state s) (inputs i) = Zmod.unsigned (N.v43767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43767 s i)) at 1.
  unfold R.v43767, N.v43767.
  rewrite ?node_43762.
  rewrite ?node_43766.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43768 (s : N.State) (i : N.Inputs) :
  R.v43768 (state s) (inputs i) = Zmod.unsigned (N.v43768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43768 s i)) at 1.
  unfold R.v43768, N.v43768.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43769 (s : N.State) (i : N.Inputs) :
  R.v43769 (state s) (inputs i) = Zmod.unsigned (N.v43769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43769 s i)) at 1.
  unfold R.v43769, N.v43769.
  rewrite ?node_11262.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43770 (s : N.State) (i : N.Inputs) :
  R.v43770 (state s) (inputs i) = Zmod.unsigned (N.v43770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43770 s i)) at 1.
  unfold R.v43770, N.v43770.
  unfold R.v6, N.v6.
  rewrite ?node_11254.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43771 (s : N.State) (i : N.Inputs) :
  R.v43771 (state s) (inputs i) = Zmod.unsigned (N.v43771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43771 s i)) at 1.
  unfold R.v43771, N.v43771.
  unfold R.v6, N.v6.
  rewrite ?node_11247.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43772 (s : N.State) (i : N.Inputs) :
  R.v43772 (state s) (inputs i) = Zmod.unsigned (N.v43772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43772 s i)) at 1.
  unfold R.v43772, N.v43772.
  rewrite ?node_43770.
  rewrite ?node_43771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43773 (s : N.State) (i : N.Inputs) :
  R.v43773 (state s) (inputs i) = Zmod.unsigned (N.v43773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43773 s i)) at 1.
  unfold R.v43773, N.v43773.
  unfold R.v16484, N.v16484.
  rewrite ?node_43772.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43774 (s : N.State) (i : N.Inputs) :
  R.v43774 (state s) (inputs i) = Zmod.unsigned (N.v43774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43774 s i)) at 1.
  unfold R.v43774, N.v43774.
  rewrite ?node_43769.
  rewrite ?node_43773.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43775 (s : N.State) (i : N.Inputs) :
  R.v43775 (state s) (inputs i) = Zmod.unsigned (N.v43775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43775 s i)) at 1.
  unfold R.v43775, N.v43775.
  unfold R.v6, N.v6.
  rewrite ?node_43774.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43776 (s : N.State) (i : N.Inputs) :
  R.v43776 (state s) (inputs i) = Zmod.unsigned (N.v43776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43776 s i)) at 1.
  unfold R.v43776, N.v43776.
  rewrite ?node_11263.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43777 (s : N.State) (i : N.Inputs) :
  R.v43777 (state s) (inputs i) = Zmod.unsigned (N.v43777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43777 s i)) at 1.
  unfold R.v43777, N.v43777.
  unfold R.v6, N.v6.
  rewrite ?node_11429.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43778 (s : N.State) (i : N.Inputs) :
  R.v43778 (state s) (inputs i) = Zmod.unsigned (N.v43778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43778 s i)) at 1.
  unfold R.v43778, N.v43778.
  rewrite ?node_43776.
  rewrite ?node_43777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43779 (s : N.State) (i : N.Inputs) :
  R.v43779 (state s) (inputs i) = Zmod.unsigned (N.v43779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43779 s i)) at 1.
  unfold R.v43779, N.v43779.
  rewrite ?node_43775.
  rewrite ?node_43778.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43780 (s : N.State) (i : N.Inputs) :
  R.v43780 (state s) (inputs i) = Zmod.unsigned (N.v43780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43780 s i)) at 1.
  unfold R.v43780, N.v43780.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43781 (s : N.State) (i : N.Inputs) :
  R.v43781 (state s) (inputs i) = Zmod.unsigned (N.v43781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43781 s i)) at 1.
  unfold R.v43781, N.v43781.
  rewrite ?node_11274.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43782 (s : N.State) (i : N.Inputs) :
  R.v43782 (state s) (inputs i) = Zmod.unsigned (N.v43782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43782 s i)) at 1.
  unfold R.v43782, N.v43782.
  unfold R.v6, N.v6.
  rewrite ?node_11270.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43783 (s : N.State) (i : N.Inputs) :
  R.v43783 (state s) (inputs i) = Zmod.unsigned (N.v43783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43783 s i)) at 1.
  unfold R.v43783, N.v43783.
  unfold R.v6, N.v6.
  rewrite ?node_11263.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43784 (s : N.State) (i : N.Inputs) :
  R.v43784 (state s) (inputs i) = Zmod.unsigned (N.v43784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43784 s i)) at 1.
  unfold R.v43784, N.v43784.
  rewrite ?node_43782.
  rewrite ?node_43783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43785 (s : N.State) (i : N.Inputs) :
  R.v43785 (state s) (inputs i) = Zmod.unsigned (N.v43785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43785 s i)) at 1.
  unfold R.v43785, N.v43785.
  unfold R.v16484, N.v16484.
  rewrite ?node_43784.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43786 (s : N.State) (i : N.Inputs) :
  R.v43786 (state s) (inputs i) = Zmod.unsigned (N.v43786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43786 s i)) at 1.
  unfold R.v43786, N.v43786.
  rewrite ?node_43781.
  rewrite ?node_43785.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43787 (s : N.State) (i : N.Inputs) :
  R.v43787 (state s) (inputs i) = Zmod.unsigned (N.v43787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43787 s i)) at 1.
  unfold R.v43787, N.v43787.
  unfold R.v6, N.v6.
  rewrite ?node_43786.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43788 (s : N.State) (i : N.Inputs) :
  R.v43788 (state s) (inputs i) = Zmod.unsigned (N.v43788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43788 s i)) at 1.
  unfold R.v43788, N.v43788.
  rewrite ?node_11275.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43789 (s : N.State) (i : N.Inputs) :
  R.v43789 (state s) (inputs i) = Zmod.unsigned (N.v43789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43789 s i)) at 1.
  unfold R.v43789, N.v43789.
  unfold R.v6, N.v6.
  rewrite ?node_11508.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43790 (s : N.State) (i : N.Inputs) :
  R.v43790 (state s) (inputs i) = Zmod.unsigned (N.v43790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43790 s i)) at 1.
  unfold R.v43790, N.v43790.
  rewrite ?node_43788.
  rewrite ?node_43789.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43791 (s : N.State) (i : N.Inputs) :
  R.v43791 (state s) (inputs i) = Zmod.unsigned (N.v43791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43791 s i)) at 1.
  unfold R.v43791, N.v43791.
  rewrite ?node_43787.
  rewrite ?node_43790.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43792 (s : N.State) (i : N.Inputs) :
  R.v43792 (state s) (inputs i) = Zmod.unsigned (N.v43792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43792 s i)) at 1.
  unfold R.v43792, N.v43792.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43793 (s : N.State) (i : N.Inputs) :
  R.v43793 (state s) (inputs i) = Zmod.unsigned (N.v43793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43793 s i)) at 1.
  unfold R.v43793, N.v43793.
  rewrite ?node_11304.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43794 (s : N.State) (i : N.Inputs) :
  R.v43794 (state s) (inputs i) = Zmod.unsigned (N.v43794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43794 s i)) at 1.
  unfold R.v43794, N.v43794.
  rewrite ?node_11300.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43795 (s : N.State) (i : N.Inputs) :
  R.v43795 (state s) (inputs i) = Zmod.unsigned (N.v43795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43795 s i)) at 1.
  unfold R.v43795, N.v43795.
  rewrite ?node_11297.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43796 (s : N.State) (i : N.Inputs) :
  R.v43796 (state s) (inputs i) = Zmod.unsigned (N.v43796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43796 s i)) at 1.
  unfold R.v43796, N.v43796.
  unfold R.v6, N.v6.
  rewrite ?node_11289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43797 (s : N.State) (i : N.Inputs) :
  R.v43797 (state s) (inputs i) = Zmod.unsigned (N.v43797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43797 s i)) at 1.
  unfold R.v43797, N.v43797.
  unfold R.v6, N.v6.
  rewrite ?node_11282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43798 (s : N.State) (i : N.Inputs) :
  R.v43798 (state s) (inputs i) = Zmod.unsigned (N.v43798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43798 s i)) at 1.
  unfold R.v43798, N.v43798.
  rewrite ?node_43796.
  rewrite ?node_43797.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43799 (s : N.State) (i : N.Inputs) :
  R.v43799 (state s) (inputs i) = Zmod.unsigned (N.v43799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43799 s i)) at 1.
  unfold R.v43799, N.v43799.
  unfold R.v16484, N.v16484.
  rewrite ?node_43798.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43800 (s : N.State) (i : N.Inputs) :
  R.v43800 (state s) (inputs i) = Zmod.unsigned (N.v43800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43800 s i)) at 1.
  unfold R.v43800, N.v43800.
  rewrite ?node_43793.
  rewrite ?node_43794.
  rewrite ?node_43795.
  rewrite ?node_43799.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43801 (s : N.State) (i : N.Inputs) :
  R.v43801 (state s) (inputs i) = Zmod.unsigned (N.v43801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43801 s i)) at 1.
  unfold R.v43801, N.v43801.
  unfold R.v6, N.v6.
  rewrite ?node_43800.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43802 (s : N.State) (i : N.Inputs) :
  R.v43802 (state s) (inputs i) = Zmod.unsigned (N.v43802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43802 s i)) at 1.
  unfold R.v43802, N.v43802.
  rewrite ?node_11305.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43803 (s : N.State) (i : N.Inputs) :
  R.v43803 (state s) (inputs i) = Zmod.unsigned (N.v43803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43803 s i)) at 1.
  unfold R.v43803, N.v43803.
  unfold R.v6, N.v6.
  rewrite ?node_11459.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43804 (s : N.State) (i : N.Inputs) :
  R.v43804 (state s) (inputs i) = Zmod.unsigned (N.v43804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43804 s i)) at 1.
  unfold R.v43804, N.v43804.
  unfold R.v6, N.v6.
  rewrite ?node_11511.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43805 (s : N.State) (i : N.Inputs) :
  R.v43805 (state s) (inputs i) = Zmod.unsigned (N.v43805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43805 s i)) at 1.
  unfold R.v43805, N.v43805.
  rewrite ?node_43802.
  rewrite ?node_43803.
  rewrite ?node_43804.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43806 (s : N.State) (i : N.Inputs) :
  R.v43806 (state s) (inputs i) = Zmod.unsigned (N.v43806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43806 s i)) at 1.
  unfold R.v43806, N.v43806.
  rewrite ?node_43801.
  rewrite ?node_43805.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43807 (s : N.State) (i : N.Inputs) :
  R.v43807 (state s) (inputs i) = Zmod.unsigned (N.v43807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43807 s i)) at 1.
  unfold R.v43807, N.v43807.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43808 (s : N.State) (i : N.Inputs) :
  R.v43808 (state s) (inputs i) = Zmod.unsigned (N.v43808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43808 s i)) at 1.
  unfold R.v43808, N.v43808.
  rewrite ?node_11297.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43809 (s : N.State) (i : N.Inputs) :
  R.v43809 (state s) (inputs i) = Zmod.unsigned (N.v43809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43809 s i)) at 1.
  unfold R.v43809, N.v43809.
  unfold R.v6, N.v6.
  rewrite ?node_11289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43810 (s : N.State) (i : N.Inputs) :
  R.v43810 (state s) (inputs i) = Zmod.unsigned (N.v43810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43810 s i)) at 1.
  unfold R.v43810, N.v43810.
  unfold R.v6, N.v6.
  rewrite ?node_11282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43811 (s : N.State) (i : N.Inputs) :
  R.v43811 (state s) (inputs i) = Zmod.unsigned (N.v43811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43811 s i)) at 1.
  unfold R.v43811, N.v43811.
  rewrite ?node_43809.
  rewrite ?node_43810.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43812 (s : N.State) (i : N.Inputs) :
  R.v43812 (state s) (inputs i) = Zmod.unsigned (N.v43812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43812 s i)) at 1.
  unfold R.v43812, N.v43812.
  unfold R.v16484, N.v16484.
  rewrite ?node_43811.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43813 (s : N.State) (i : N.Inputs) :
  R.v43813 (state s) (inputs i) = Zmod.unsigned (N.v43813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43813 s i)) at 1.
  unfold R.v43813, N.v43813.
  rewrite ?node_43808.
  rewrite ?node_43812.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43814 (s : N.State) (i : N.Inputs) :
  R.v43814 (state s) (inputs i) = Zmod.unsigned (N.v43814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43814 s i)) at 1.
  unfold R.v43814, N.v43814.
  unfold R.v6, N.v6.
  rewrite ?node_43813.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43815 (s : N.State) (i : N.Inputs) :
  R.v43815 (state s) (inputs i) = Zmod.unsigned (N.v43815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43815 s i)) at 1.
  unfold R.v43815, N.v43815.
  rewrite ?node_11298.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43816 (s : N.State) (i : N.Inputs) :
  R.v43816 (state s) (inputs i) = Zmod.unsigned (N.v43816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43816 s i)) at 1.
  unfold R.v43816, N.v43816.
  unfold R.v6, N.v6.
  rewrite ?node_11459.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43817 (s : N.State) (i : N.Inputs) :
  R.v43817 (state s) (inputs i) = Zmod.unsigned (N.v43817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43817 s i)) at 1.
  unfold R.v43817, N.v43817.
  rewrite ?node_43815.
  rewrite ?node_43816.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43818 (s : N.State) (i : N.Inputs) :
  R.v43818 (state s) (inputs i) = Zmod.unsigned (N.v43818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43818 s i)) at 1.
  unfold R.v43818, N.v43818.
  rewrite ?node_43814.
  rewrite ?node_43817.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43819 (s : N.State) (i : N.Inputs) :
  R.v43819 (state s) (inputs i) = Zmod.unsigned (N.v43819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43819 s i)) at 1.
  unfold R.v43819, N.v43819.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43820 (s : N.State) (i : N.Inputs) :
  R.v43820 (state s) (inputs i) = Zmod.unsigned (N.v43820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43820 s i)) at 1.
  unfold R.v43820, N.v43820.
  rewrite ?node_11304.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43821 (s : N.State) (i : N.Inputs) :
  R.v43821 (state s) (inputs i) = Zmod.unsigned (N.v43821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43821 s i)) at 1.
  unfold R.v43821, N.v43821.
  unfold R.v6, N.v6.
  rewrite ?node_11300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43822 (s : N.State) (i : N.Inputs) :
  R.v43822 (state s) (inputs i) = Zmod.unsigned (N.v43822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43822 s i)) at 1.
  unfold R.v43822, N.v43822.
  unfold R.v6, N.v6.
  rewrite ?node_11298.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43823 (s : N.State) (i : N.Inputs) :
  R.v43823 (state s) (inputs i) = Zmod.unsigned (N.v43823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43823 s i)) at 1.
  unfold R.v43823, N.v43823.
  rewrite ?node_43821.
  rewrite ?node_43822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43824 (s : N.State) (i : N.Inputs) :
  R.v43824 (state s) (inputs i) = Zmod.unsigned (N.v43824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43824 s i)) at 1.
  unfold R.v43824, N.v43824.
  unfold R.v16484, N.v16484.
  rewrite ?node_43823.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43825 (s : N.State) (i : N.Inputs) :
  R.v43825 (state s) (inputs i) = Zmod.unsigned (N.v43825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43825 s i)) at 1.
  unfold R.v43825, N.v43825.
  rewrite ?node_43820.
  rewrite ?node_43824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43826 (s : N.State) (i : N.Inputs) :
  R.v43826 (state s) (inputs i) = Zmod.unsigned (N.v43826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43826 s i)) at 1.
  unfold R.v43826, N.v43826.
  unfold R.v6, N.v6.
  rewrite ?node_43825.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43827 (s : N.State) (i : N.Inputs) :
  R.v43827 (state s) (inputs i) = Zmod.unsigned (N.v43827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43827 s i)) at 1.
  unfold R.v43827, N.v43827.
  rewrite ?node_11305.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43828 (s : N.State) (i : N.Inputs) :
  R.v43828 (state s) (inputs i) = Zmod.unsigned (N.v43828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43828 s i)) at 1.
  unfold R.v43828, N.v43828.
  unfold R.v6, N.v6.
  rewrite ?node_11511.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43829 (s : N.State) (i : N.Inputs) :
  R.v43829 (state s) (inputs i) = Zmod.unsigned (N.v43829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43829 s i)) at 1.
  unfold R.v43829, N.v43829.
  rewrite ?node_43827.
  rewrite ?node_43828.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43830 (s : N.State) (i : N.Inputs) :
  R.v43830 (state s) (inputs i) = Zmod.unsigned (N.v43830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43830 s i)) at 1.
  unfold R.v43830, N.v43830.
  rewrite ?node_43826.
  rewrite ?node_43829.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43831 (s : N.State) (i : N.Inputs) :
  R.v43831 (state s) (inputs i) = Zmod.unsigned (N.v43831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43831 s i)) at 1.
  unfold R.v43831, N.v43831.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43832 (s : N.State) (i : N.Inputs) :
  R.v43832 (state s) (inputs i) = Zmod.unsigned (N.v43832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43832 s i)) at 1.
  unfold R.v43832, N.v43832.
  rewrite ?node_11324.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43833 (s : N.State) (i : N.Inputs) :
  R.v43833 (state s) (inputs i) = Zmod.unsigned (N.v43833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43833 s i)) at 1.
  unfold R.v43833, N.v43833.
  rewrite ?node_11320.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43834 (s : N.State) (i : N.Inputs) :
  R.v43834 (state s) (inputs i) = Zmod.unsigned (N.v43834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43834 s i)) at 1.
  unfold R.v43834, N.v43834.
  rewrite ?node_11316.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43835 (s : N.State) (i : N.Inputs) :
  R.v43835 (state s) (inputs i) = Zmod.unsigned (N.v43835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43835 s i)) at 1.
  unfold R.v43835, N.v43835.
  unfold R.v6, N.v6.
  rewrite ?node_11312.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43836 (s : N.State) (i : N.Inputs) :
  R.v43836 (state s) (inputs i) = Zmod.unsigned (N.v43836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43836 s i)) at 1.
  unfold R.v43836, N.v43836.
  unfold R.v6, N.v6.
  rewrite ?node_11309.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43837 (s : N.State) (i : N.Inputs) :
  R.v43837 (state s) (inputs i) = Zmod.unsigned (N.v43837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43837 s i)) at 1.
  unfold R.v43837, N.v43837.
  rewrite ?node_43835.
  rewrite ?node_43836.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43838 (s : N.State) (i : N.Inputs) :
  R.v43838 (state s) (inputs i) = Zmod.unsigned (N.v43838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43838 s i)) at 1.
  unfold R.v43838, N.v43838.
  unfold R.v16484, N.v16484.
  rewrite ?node_43837.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43839 (s : N.State) (i : N.Inputs) :
  R.v43839 (state s) (inputs i) = Zmod.unsigned (N.v43839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43839 s i)) at 1.
  unfold R.v43839, N.v43839.
  rewrite ?node_43832.
  rewrite ?node_43833.
  rewrite ?node_43834.
  rewrite ?node_43838.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43840 (s : N.State) (i : N.Inputs) :
  R.v43840 (state s) (inputs i) = Zmod.unsigned (N.v43840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43840 s i)) at 1.
  unfold R.v43840, N.v43840.
  unfold R.v6, N.v6.
  rewrite ?node_43839.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43841 (s : N.State) (i : N.Inputs) :
  R.v43841 (state s) (inputs i) = Zmod.unsigned (N.v43841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43841 s i)) at 1.
  unfold R.v43841, N.v43841.
  rewrite ?node_11325.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43842 (s : N.State) (i : N.Inputs) :
  R.v43842 (state s) (inputs i) = Zmod.unsigned (N.v43842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43842 s i)) at 1.
  unfold R.v43842, N.v43842.
  unfold R.v6, N.v6.
  rewrite ?node_11479.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43843 (s : N.State) (i : N.Inputs) :
  R.v43843 (state s) (inputs i) = Zmod.unsigned (N.v43843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43843 s i)) at 1.
  unfold R.v43843, N.v43843.
  unfold R.v6, N.v6.
  rewrite ?node_11515.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43844 (s : N.State) (i : N.Inputs) :
  R.v43844 (state s) (inputs i) = Zmod.unsigned (N.v43844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43844 s i)) at 1.
  unfold R.v43844, N.v43844.
  rewrite ?node_43841.
  rewrite ?node_43842.
  rewrite ?node_43843.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43845 (s : N.State) (i : N.Inputs) :
  R.v43845 (state s) (inputs i) = Zmod.unsigned (N.v43845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43845 s i)) at 1.
  unfold R.v43845, N.v43845.
  rewrite ?node_43840.
  rewrite ?node_43844.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43846 (s : N.State) (i : N.Inputs) :
  R.v43846 (state s) (inputs i) = Zmod.unsigned (N.v43846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43846 s i)) at 1.
  unfold R.v43846, N.v43846.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43847 (s : N.State) (i : N.Inputs) :
  R.v43847 (state s) (inputs i) = Zmod.unsigned (N.v43847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43847 s i)) at 1.
  unfold R.v43847, N.v43847.
  rewrite ?node_11316.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43848 (s : N.State) (i : N.Inputs) :
  R.v43848 (state s) (inputs i) = Zmod.unsigned (N.v43848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43848 s i)) at 1.
  unfold R.v43848, N.v43848.
  unfold R.v6, N.v6.
  rewrite ?node_11312.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43849 (s : N.State) (i : N.Inputs) :
  R.v43849 (state s) (inputs i) = Zmod.unsigned (N.v43849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43849 s i)) at 1.
  unfold R.v43849, N.v43849.
  unfold R.v6, N.v6.
  rewrite ?node_11309.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43850 (s : N.State) (i : N.Inputs) :
  R.v43850 (state s) (inputs i) = Zmod.unsigned (N.v43850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43850 s i)) at 1.
  unfold R.v43850, N.v43850.
  rewrite ?node_43848.
  rewrite ?node_43849.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43851 (s : N.State) (i : N.Inputs) :
  R.v43851 (state s) (inputs i) = Zmod.unsigned (N.v43851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43851 s i)) at 1.
  unfold R.v43851, N.v43851.
  unfold R.v16484, N.v16484.
  rewrite ?node_43850.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43852 (s : N.State) (i : N.Inputs) :
  R.v43852 (state s) (inputs i) = Zmod.unsigned (N.v43852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43852 s i)) at 1.
  unfold R.v43852, N.v43852.
  rewrite ?node_43847.
  rewrite ?node_43851.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43853 (s : N.State) (i : N.Inputs) :
  R.v43853 (state s) (inputs i) = Zmod.unsigned (N.v43853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43853 s i)) at 1.
  unfold R.v43853, N.v43853.
  unfold R.v6, N.v6.
  rewrite ?node_43852.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43854 (s : N.State) (i : N.Inputs) :
  R.v43854 (state s) (inputs i) = Zmod.unsigned (N.v43854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43854 s i)) at 1.
  unfold R.v43854, N.v43854.
  rewrite ?node_11317.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43855 (s : N.State) (i : N.Inputs) :
  R.v43855 (state s) (inputs i) = Zmod.unsigned (N.v43855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43855 s i)) at 1.
  unfold R.v43855, N.v43855.
  unfold R.v6, N.v6.
  rewrite ?node_11479.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43856 (s : N.State) (i : N.Inputs) :
  R.v43856 (state s) (inputs i) = Zmod.unsigned (N.v43856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43856 s i)) at 1.
  unfold R.v43856, N.v43856.
  rewrite ?node_43854.
  rewrite ?node_43855.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43857 (s : N.State) (i : N.Inputs) :
  R.v43857 (state s) (inputs i) = Zmod.unsigned (N.v43857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43857 s i)) at 1.
  unfold R.v43857, N.v43857.
  rewrite ?node_43853.
  rewrite ?node_43856.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43858 (s : N.State) (i : N.Inputs) :
  R.v43858 (state s) (inputs i) = Zmod.unsigned (N.v43858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43858 s i)) at 1.
  unfold R.v43858, N.v43858.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43859 (s : N.State) (i : N.Inputs) :
  R.v43859 (state s) (inputs i) = Zmod.unsigned (N.v43859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43859 s i)) at 1.
  unfold R.v43859, N.v43859.
  rewrite ?node_11324.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43860 (s : N.State) (i : N.Inputs) :
  R.v43860 (state s) (inputs i) = Zmod.unsigned (N.v43860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43860 s i)) at 1.
  unfold R.v43860, N.v43860.
  unfold R.v6, N.v6.
  rewrite ?node_11320.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43861 (s : N.State) (i : N.Inputs) :
  R.v43861 (state s) (inputs i) = Zmod.unsigned (N.v43861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43861 s i)) at 1.
  unfold R.v43861, N.v43861.
  unfold R.v6, N.v6.
  rewrite ?node_11317.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43862 (s : N.State) (i : N.Inputs) :
  R.v43862 (state s) (inputs i) = Zmod.unsigned (N.v43862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43862 s i)) at 1.
  unfold R.v43862, N.v43862.
  rewrite ?node_43860.
  rewrite ?node_43861.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43863 (s : N.State) (i : N.Inputs) :
  R.v43863 (state s) (inputs i) = Zmod.unsigned (N.v43863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43863 s i)) at 1.
  unfold R.v43863, N.v43863.
  unfold R.v16484, N.v16484.
  rewrite ?node_43862.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43864 (s : N.State) (i : N.Inputs) :
  R.v43864 (state s) (inputs i) = Zmod.unsigned (N.v43864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43864 s i)) at 1.
  unfold R.v43864, N.v43864.
  rewrite ?node_43859.
  rewrite ?node_43863.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43865 (s : N.State) (i : N.Inputs) :
  R.v43865 (state s) (inputs i) = Zmod.unsigned (N.v43865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43865 s i)) at 1.
  unfold R.v43865, N.v43865.
  unfold R.v6, N.v6.
  rewrite ?node_43864.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43866 (s : N.State) (i : N.Inputs) :
  R.v43866 (state s) (inputs i) = Zmod.unsigned (N.v43866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43866 s i)) at 1.
  unfold R.v43866, N.v43866.
  rewrite ?node_11325.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43867 (s : N.State) (i : N.Inputs) :
  R.v43867 (state s) (inputs i) = Zmod.unsigned (N.v43867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43867 s i)) at 1.
  unfold R.v43867, N.v43867.
  unfold R.v6, N.v6.
  rewrite ?node_11515.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43868 (s : N.State) (i : N.Inputs) :
  R.v43868 (state s) (inputs i) = Zmod.unsigned (N.v43868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43868 s i)) at 1.
  unfold R.v43868, N.v43868.
  rewrite ?node_43866.
  rewrite ?node_43867.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43869 (s : N.State) (i : N.Inputs) :
  R.v43869 (state s) (inputs i) = Zmod.unsigned (N.v43869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43869 s i)) at 1.
  unfold R.v43869, N.v43869.
  rewrite ?node_43865.
  rewrite ?node_43868.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43870 (s : N.State) (i : N.Inputs) :
  R.v43870 (state s) (inputs i) = Zmod.unsigned (N.v43870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43870 s i)) at 1.
  unfold R.v43870, N.v43870.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43871 (s : N.State) (i : N.Inputs) :
  R.v43871 (state s) (inputs i) = Zmod.unsigned (N.v43871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43871 s i)) at 1.
  unfold R.v43871, N.v43871.
  rewrite ?node_11344.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43872 (s : N.State) (i : N.Inputs) :
  R.v43872 (state s) (inputs i) = Zmod.unsigned (N.v43872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43872 s i)) at 1.
  unfold R.v43872, N.v43872.
  rewrite ?node_11340.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43873 (s : N.State) (i : N.Inputs) :
  R.v43873 (state s) (inputs i) = Zmod.unsigned (N.v43873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43873 s i)) at 1.
  unfold R.v43873, N.v43873.
  rewrite ?node_11336.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43874 (s : N.State) (i : N.Inputs) :
  R.v43874 (state s) (inputs i) = Zmod.unsigned (N.v43874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43874 s i)) at 1.
  unfold R.v43874, N.v43874.
  unfold R.v6, N.v6.
  rewrite ?node_11332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43875 (s : N.State) (i : N.Inputs) :
  R.v43875 (state s) (inputs i) = Zmod.unsigned (N.v43875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43875 s i)) at 1.
  unfold R.v43875, N.v43875.
  unfold R.v6, N.v6.
  rewrite ?node_11329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43876 (s : N.State) (i : N.Inputs) :
  R.v43876 (state s) (inputs i) = Zmod.unsigned (N.v43876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43876 s i)) at 1.
  unfold R.v43876, N.v43876.
  rewrite ?node_43874.
  rewrite ?node_43875.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43877 (s : N.State) (i : N.Inputs) :
  R.v43877 (state s) (inputs i) = Zmod.unsigned (N.v43877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43877 s i)) at 1.
  unfold R.v43877, N.v43877.
  unfold R.v16484, N.v16484.
  rewrite ?node_43876.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43878 (s : N.State) (i : N.Inputs) :
  R.v43878 (state s) (inputs i) = Zmod.unsigned (N.v43878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43878 s i)) at 1.
  unfold R.v43878, N.v43878.
  rewrite ?node_43871.
  rewrite ?node_43872.
  rewrite ?node_43873.
  rewrite ?node_43877.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43879 (s : N.State) (i : N.Inputs) :
  R.v43879 (state s) (inputs i) = Zmod.unsigned (N.v43879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43879 s i)) at 1.
  unfold R.v43879, N.v43879.
  unfold R.v6, N.v6.
  rewrite ?node_43878.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43880 (s : N.State) (i : N.Inputs) :
  R.v43880 (state s) (inputs i) = Zmod.unsigned (N.v43880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43880 s i)) at 1.
  unfold R.v43880, N.v43880.
  rewrite ?node_11345.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43881 (s : N.State) (i : N.Inputs) :
  R.v43881 (state s) (inputs i) = Zmod.unsigned (N.v43881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43881 s i)) at 1.
  unfold R.v43881, N.v43881.
  unfold R.v6, N.v6.
  rewrite ?node_11499.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43882 (s : N.State) (i : N.Inputs) :
  R.v43882 (state s) (inputs i) = Zmod.unsigned (N.v43882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43882 s i)) at 1.
  unfold R.v43882, N.v43882.
  unfold R.v6, N.v6.
  rewrite ?node_11519.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43883 (s : N.State) (i : N.Inputs) :
  R.v43883 (state s) (inputs i) = Zmod.unsigned (N.v43883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43883 s i)) at 1.
  unfold R.v43883, N.v43883.
  rewrite ?node_43880.
  rewrite ?node_43881.
  rewrite ?node_43882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43884 (s : N.State) (i : N.Inputs) :
  R.v43884 (state s) (inputs i) = Zmod.unsigned (N.v43884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43884 s i)) at 1.
  unfold R.v43884, N.v43884.
  rewrite ?node_43879.
  rewrite ?node_43883.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43885 (s : N.State) (i : N.Inputs) :
  R.v43885 (state s) (inputs i) = Zmod.unsigned (N.v43885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43885 s i)) at 1.
  unfold R.v43885, N.v43885.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43886 (s : N.State) (i : N.Inputs) :
  R.v43886 (state s) (inputs i) = Zmod.unsigned (N.v43886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43886 s i)) at 1.
  unfold R.v43886, N.v43886.
  rewrite ?node_11336.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43887 (s : N.State) (i : N.Inputs) :
  R.v43887 (state s) (inputs i) = Zmod.unsigned (N.v43887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43887 s i)) at 1.
  unfold R.v43887, N.v43887.
  unfold R.v6, N.v6.
  rewrite ?node_11332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43888 (s : N.State) (i : N.Inputs) :
  R.v43888 (state s) (inputs i) = Zmod.unsigned (N.v43888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43888 s i)) at 1.
  unfold R.v43888, N.v43888.
  unfold R.v6, N.v6.
  rewrite ?node_11329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43889 (s : N.State) (i : N.Inputs) :
  R.v43889 (state s) (inputs i) = Zmod.unsigned (N.v43889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43889 s i)) at 1.
  unfold R.v43889, N.v43889.
  rewrite ?node_43887.
  rewrite ?node_43888.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43890 (s : N.State) (i : N.Inputs) :
  R.v43890 (state s) (inputs i) = Zmod.unsigned (N.v43890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43890 s i)) at 1.
  unfold R.v43890, N.v43890.
  unfold R.v16484, N.v16484.
  rewrite ?node_43889.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43891 (s : N.State) (i : N.Inputs) :
  R.v43891 (state s) (inputs i) = Zmod.unsigned (N.v43891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43891 s i)) at 1.
  unfold R.v43891, N.v43891.
  rewrite ?node_43886.
  rewrite ?node_43890.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43892 (s : N.State) (i : N.Inputs) :
  R.v43892 (state s) (inputs i) = Zmod.unsigned (N.v43892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43892 s i)) at 1.
  unfold R.v43892, N.v43892.
  unfold R.v6, N.v6.
  rewrite ?node_43891.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43893 (s : N.State) (i : N.Inputs) :
  R.v43893 (state s) (inputs i) = Zmod.unsigned (N.v43893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43893 s i)) at 1.
  unfold R.v43893, N.v43893.
  rewrite ?node_11337.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43894 (s : N.State) (i : N.Inputs) :
  R.v43894 (state s) (inputs i) = Zmod.unsigned (N.v43894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43894 s i)) at 1.
  unfold R.v43894, N.v43894.
  unfold R.v6, N.v6.
  rewrite ?node_11499.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43895 (s : N.State) (i : N.Inputs) :
  R.v43895 (state s) (inputs i) = Zmod.unsigned (N.v43895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43895 s i)) at 1.
  unfold R.v43895, N.v43895.
  rewrite ?node_43893.
  rewrite ?node_43894.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43896 (s : N.State) (i : N.Inputs) :
  R.v43896 (state s) (inputs i) = Zmod.unsigned (N.v43896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43896 s i)) at 1.
  unfold R.v43896, N.v43896.
  rewrite ?node_43892.
  rewrite ?node_43895.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43897 (s : N.State) (i : N.Inputs) :
  R.v43897 (state s) (inputs i) = Zmod.unsigned (N.v43897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43897 s i)) at 1.
  unfold R.v43897, N.v43897.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43898 (s : N.State) (i : N.Inputs) :
  R.v43898 (state s) (inputs i) = Zmod.unsigned (N.v43898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43898 s i)) at 1.
  unfold R.v43898, N.v43898.
  rewrite ?node_11344.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43899 (s : N.State) (i : N.Inputs) :
  R.v43899 (state s) (inputs i) = Zmod.unsigned (N.v43899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43899 s i)) at 1.
  unfold R.v43899, N.v43899.
  unfold R.v6, N.v6.
  rewrite ?node_11340.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43900 (s : N.State) (i : N.Inputs) :
  R.v43900 (state s) (inputs i) = Zmod.unsigned (N.v43900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43900 s i)) at 1.
  unfold R.v43900, N.v43900.
  unfold R.v6, N.v6.
  rewrite ?node_11337.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43901 (s : N.State) (i : N.Inputs) :
  R.v43901 (state s) (inputs i) = Zmod.unsigned (N.v43901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43901 s i)) at 1.
  unfold R.v43901, N.v43901.
  rewrite ?node_43899.
  rewrite ?node_43900.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43902 (s : N.State) (i : N.Inputs) :
  R.v43902 (state s) (inputs i) = Zmod.unsigned (N.v43902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43902 s i)) at 1.
  unfold R.v43902, N.v43902.
  unfold R.v16484, N.v16484.
  rewrite ?node_43901.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43903 (s : N.State) (i : N.Inputs) :
  R.v43903 (state s) (inputs i) = Zmod.unsigned (N.v43903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43903 s i)) at 1.
  unfold R.v43903, N.v43903.
  rewrite ?node_43898.
  rewrite ?node_43902.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43904 (s : N.State) (i : N.Inputs) :
  R.v43904 (state s) (inputs i) = Zmod.unsigned (N.v43904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43904 s i)) at 1.
  unfold R.v43904, N.v43904.
  unfold R.v6, N.v6.
  rewrite ?node_43903.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43905 (s : N.State) (i : N.Inputs) :
  R.v43905 (state s) (inputs i) = Zmod.unsigned (N.v43905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43905 s i)) at 1.
  unfold R.v43905, N.v43905.
  rewrite ?node_11345.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43906 (s : N.State) (i : N.Inputs) :
  R.v43906 (state s) (inputs i) = Zmod.unsigned (N.v43906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43906 s i)) at 1.
  unfold R.v43906, N.v43906.
  unfold R.v6, N.v6.
  rewrite ?node_11519.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43907 (s : N.State) (i : N.Inputs) :
  R.v43907 (state s) (inputs i) = Zmod.unsigned (N.v43907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43907 s i)) at 1.
  unfold R.v43907, N.v43907.
  rewrite ?node_43905.
  rewrite ?node_43906.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43908 (s : N.State) (i : N.Inputs) :
  R.v43908 (state s) (inputs i) = Zmod.unsigned (N.v43908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43908 s i)) at 1.
  unfold R.v43908, N.v43908.
  rewrite ?node_43904.
  rewrite ?node_43907.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43909 (s : N.State) (i : N.Inputs) :
  R.v43909 (state s) (inputs i) = Zmod.unsigned (N.v43909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43909 s i)) at 1.
  unfold R.v43909, N.v43909.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43910 (s : N.State) (i : N.Inputs) :
  R.v43910 (state s) (inputs i) = Zmod.unsigned (N.v43910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43910 s i)) at 1.
  unfold R.v43910, N.v43910.
  rewrite ?node_11429.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43911 (s : N.State) (i : N.Inputs) :
  R.v43911 (state s) (inputs i) = Zmod.unsigned (N.v43911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43911 s i)) at 1.
  unfold R.v43911, N.v43911.
  rewrite ?node_11425.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43912 (s : N.State) (i : N.Inputs) :
  R.v43912 (state s) (inputs i) = Zmod.unsigned (N.v43912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43912 s i)) at 1.
  unfold R.v43912, N.v43912.
  rewrite ?node_11417.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43913 (s : N.State) (i : N.Inputs) :
  R.v43913 (state s) (inputs i) = Zmod.unsigned (N.v43913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43913 s i)) at 1.
  unfold R.v43913, N.v43913.
  unfold R.v6, N.v6.
  rewrite ?node_11409.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43914 (s : N.State) (i : N.Inputs) :
  R.v43914 (state s) (inputs i) = Zmod.unsigned (N.v43914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43914 s i)) at 1.
  unfold R.v43914, N.v43914.
  unfold R.v6, N.v6.
  rewrite ?node_11402.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43915 (s : N.State) (i : N.Inputs) :
  R.v43915 (state s) (inputs i) = Zmod.unsigned (N.v43915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43915 s i)) at 1.
  unfold R.v43915, N.v43915.
  rewrite ?node_43913.
  rewrite ?node_43914.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43916 (s : N.State) (i : N.Inputs) :
  R.v43916 (state s) (inputs i) = Zmod.unsigned (N.v43916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43916 s i)) at 1.
  unfold R.v43916, N.v43916.
  unfold R.v16484, N.v16484.
  rewrite ?node_43915.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43917 (s : N.State) (i : N.Inputs) :
  R.v43917 (state s) (inputs i) = Zmod.unsigned (N.v43917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43917 s i)) at 1.
  unfold R.v43917, N.v43917.
  rewrite ?node_43910.
  rewrite ?node_43911.
  rewrite ?node_43912.
  rewrite ?node_43916.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43918 (s : N.State) (i : N.Inputs) :
  R.v43918 (state s) (inputs i) = Zmod.unsigned (N.v43918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43918 s i)) at 1.
  unfold R.v43918, N.v43918.
  unfold R.v6, N.v6.
  rewrite ?node_43917.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43919 (s : N.State) (i : N.Inputs) :
  R.v43919 (state s) (inputs i) = Zmod.unsigned (N.v43919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43919 s i)) at 1.
  unfold R.v43919, N.v43919.
  rewrite ?node_11430.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43920 (s : N.State) (i : N.Inputs) :
  R.v43920 (state s) (inputs i) = Zmod.unsigned (N.v43920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43920 s i)) at 1.
  unfold R.v43920, N.v43920.
  unfold R.v6, N.v6.
  rewrite ?node_11579.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43921 (s : N.State) (i : N.Inputs) :
  R.v43921 (state s) (inputs i) = Zmod.unsigned (N.v43921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43921 s i)) at 1.
  unfold R.v43921, N.v43921.
  unfold R.v6, N.v6.
  rewrite ?node_11657.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43922 (s : N.State) (i : N.Inputs) :
  R.v43922 (state s) (inputs i) = Zmod.unsigned (N.v43922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43922 s i)) at 1.
  unfold R.v43922, N.v43922.
  rewrite ?node_43919.
  rewrite ?node_43920.
  rewrite ?node_43921.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43923 (s : N.State) (i : N.Inputs) :
  R.v43923 (state s) (inputs i) = Zmod.unsigned (N.v43923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43923 s i)) at 1.
  unfold R.v43923, N.v43923.
  rewrite ?node_43918.
  rewrite ?node_43922.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43924 (s : N.State) (i : N.Inputs) :
  R.v43924 (state s) (inputs i) = Zmod.unsigned (N.v43924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43924 s i)) at 1.
  unfold R.v43924, N.v43924.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43925 (s : N.State) (i : N.Inputs) :
  R.v43925 (state s) (inputs i) = Zmod.unsigned (N.v43925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43925 s i)) at 1.
  unfold R.v43925, N.v43925.
  rewrite ?node_11417.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43926 (s : N.State) (i : N.Inputs) :
  R.v43926 (state s) (inputs i) = Zmod.unsigned (N.v43926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43926 s i)) at 1.
  unfold R.v43926, N.v43926.
  unfold R.v6, N.v6.
  rewrite ?node_11409.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43927 (s : N.State) (i : N.Inputs) :
  R.v43927 (state s) (inputs i) = Zmod.unsigned (N.v43927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43927 s i)) at 1.
  unfold R.v43927, N.v43927.
  unfold R.v6, N.v6.
  rewrite ?node_11402.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43928 (s : N.State) (i : N.Inputs) :
  R.v43928 (state s) (inputs i) = Zmod.unsigned (N.v43928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43928 s i)) at 1.
  unfold R.v43928, N.v43928.
  rewrite ?node_43926.
  rewrite ?node_43927.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43929 (s : N.State) (i : N.Inputs) :
  R.v43929 (state s) (inputs i) = Zmod.unsigned (N.v43929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43929 s i)) at 1.
  unfold R.v43929, N.v43929.
  unfold R.v16484, N.v16484.
  rewrite ?node_43928.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43930 (s : N.State) (i : N.Inputs) :
  R.v43930 (state s) (inputs i) = Zmod.unsigned (N.v43930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43930 s i)) at 1.
  unfold R.v43930, N.v43930.
  rewrite ?node_43925.
  rewrite ?node_43929.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43931 (s : N.State) (i : N.Inputs) :
  R.v43931 (state s) (inputs i) = Zmod.unsigned (N.v43931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43931 s i)) at 1.
  unfold R.v43931, N.v43931.
  unfold R.v6, N.v6.
  rewrite ?node_43930.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43932 (s : N.State) (i : N.Inputs) :
  R.v43932 (state s) (inputs i) = Zmod.unsigned (N.v43932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43932 s i)) at 1.
  unfold R.v43932, N.v43932.
  rewrite ?node_11418.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43933 (s : N.State) (i : N.Inputs) :
  R.v43933 (state s) (inputs i) = Zmod.unsigned (N.v43933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43933 s i)) at 1.
  unfold R.v43933, N.v43933.
  unfold R.v6, N.v6.
  rewrite ?node_11579.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43934 (s : N.State) (i : N.Inputs) :
  R.v43934 (state s) (inputs i) = Zmod.unsigned (N.v43934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43934 s i)) at 1.
  unfold R.v43934, N.v43934.
  rewrite ?node_43932.
  rewrite ?node_43933.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43935 (s : N.State) (i : N.Inputs) :
  R.v43935 (state s) (inputs i) = Zmod.unsigned (N.v43935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43935 s i)) at 1.
  unfold R.v43935, N.v43935.
  rewrite ?node_43931.
  rewrite ?node_43934.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43936 (s : N.State) (i : N.Inputs) :
  R.v43936 (state s) (inputs i) = Zmod.unsigned (N.v43936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43936 s i)) at 1.
  unfold R.v43936, N.v43936.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43937 (s : N.State) (i : N.Inputs) :
  R.v43937 (state s) (inputs i) = Zmod.unsigned (N.v43937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43937 s i)) at 1.
  unfold R.v43937, N.v43937.
  rewrite ?node_11429.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43938 (s : N.State) (i : N.Inputs) :
  R.v43938 (state s) (inputs i) = Zmod.unsigned (N.v43938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43938 s i)) at 1.
  unfold R.v43938, N.v43938.
  unfold R.v6, N.v6.
  rewrite ?node_11425.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43939 (s : N.State) (i : N.Inputs) :
  R.v43939 (state s) (inputs i) = Zmod.unsigned (N.v43939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43939 s i)) at 1.
  unfold R.v43939, N.v43939.
  unfold R.v6, N.v6.
  rewrite ?node_11418.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43940 (s : N.State) (i : N.Inputs) :
  R.v43940 (state s) (inputs i) = Zmod.unsigned (N.v43940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43940 s i)) at 1.
  unfold R.v43940, N.v43940.
  rewrite ?node_43938.
  rewrite ?node_43939.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43941 (s : N.State) (i : N.Inputs) :
  R.v43941 (state s) (inputs i) = Zmod.unsigned (N.v43941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43941 s i)) at 1.
  unfold R.v43941, N.v43941.
  unfold R.v16484, N.v16484.
  rewrite ?node_43940.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43942 (s : N.State) (i : N.Inputs) :
  R.v43942 (state s) (inputs i) = Zmod.unsigned (N.v43942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43942 s i)) at 1.
  unfold R.v43942, N.v43942.
  rewrite ?node_43937.
  rewrite ?node_43941.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43943 (s : N.State) (i : N.Inputs) :
  R.v43943 (state s) (inputs i) = Zmod.unsigned (N.v43943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43943 s i)) at 1.
  unfold R.v43943, N.v43943.
  unfold R.v6, N.v6.
  rewrite ?node_43942.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43944 (s : N.State) (i : N.Inputs) :
  R.v43944 (state s) (inputs i) = Zmod.unsigned (N.v43944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43944 s i)) at 1.
  unfold R.v43944, N.v43944.
  rewrite ?node_11430.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43945 (s : N.State) (i : N.Inputs) :
  R.v43945 (state s) (inputs i) = Zmod.unsigned (N.v43945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43945 s i)) at 1.
  unfold R.v43945, N.v43945.
  unfold R.v6, N.v6.
  rewrite ?node_11657.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43946 (s : N.State) (i : N.Inputs) :
  R.v43946 (state s) (inputs i) = Zmod.unsigned (N.v43946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43946 s i)) at 1.
  unfold R.v43946, N.v43946.
  rewrite ?node_43944.
  rewrite ?node_43945.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43947 (s : N.State) (i : N.Inputs) :
  R.v43947 (state s) (inputs i) = Zmod.unsigned (N.v43947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43947 s i)) at 1.
  unfold R.v43947, N.v43947.
  rewrite ?node_43943.
  rewrite ?node_43946.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43948 (s : N.State) (i : N.Inputs) :
  R.v43948 (state s) (inputs i) = Zmod.unsigned (N.v43948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43948 s i)) at 1.
  unfold R.v43948, N.v43948.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43949 (s : N.State) (i : N.Inputs) :
  R.v43949 (state s) (inputs i) = Zmod.unsigned (N.v43949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43949 s i)) at 1.
  unfold R.v43949, N.v43949.
  rewrite ?node_11459.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43950 (s : N.State) (i : N.Inputs) :
  R.v43950 (state s) (inputs i) = Zmod.unsigned (N.v43950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43950 s i)) at 1.
  unfold R.v43950, N.v43950.
  rewrite ?node_11455.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43951 (s : N.State) (i : N.Inputs) :
  R.v43951 (state s) (inputs i) = Zmod.unsigned (N.v43951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43951 s i)) at 1.
  unfold R.v43951, N.v43951.
  rewrite ?node_11452.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43952 (s : N.State) (i : N.Inputs) :
  R.v43952 (state s) (inputs i) = Zmod.unsigned (N.v43952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43952 s i)) at 1.
  unfold R.v43952, N.v43952.
  unfold R.v6, N.v6.
  rewrite ?node_11444.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43953 (s : N.State) (i : N.Inputs) :
  R.v43953 (state s) (inputs i) = Zmod.unsigned (N.v43953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43953 s i)) at 1.
  unfold R.v43953, N.v43953.
  unfold R.v6, N.v6.
  rewrite ?node_11437.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43954 (s : N.State) (i : N.Inputs) :
  R.v43954 (state s) (inputs i) = Zmod.unsigned (N.v43954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43954 s i)) at 1.
  unfold R.v43954, N.v43954.
  rewrite ?node_43952.
  rewrite ?node_43953.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43955 (s : N.State) (i : N.Inputs) :
  R.v43955 (state s) (inputs i) = Zmod.unsigned (N.v43955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43955 s i)) at 1.
  unfold R.v43955, N.v43955.
  unfold R.v16484, N.v16484.
  rewrite ?node_43954.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43956 (s : N.State) (i : N.Inputs) :
  R.v43956 (state s) (inputs i) = Zmod.unsigned (N.v43956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43956 s i)) at 1.
  unfold R.v43956, N.v43956.
  rewrite ?node_43949.
  rewrite ?node_43950.
  rewrite ?node_43951.
  rewrite ?node_43955.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43957 (s : N.State) (i : N.Inputs) :
  R.v43957 (state s) (inputs i) = Zmod.unsigned (N.v43957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43957 s i)) at 1.
  unfold R.v43957, N.v43957.
  unfold R.v6, N.v6.
  rewrite ?node_43956.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43958 (s : N.State) (i : N.Inputs) :
  R.v43958 (state s) (inputs i) = Zmod.unsigned (N.v43958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43958 s i)) at 1.
  unfold R.v43958, N.v43958.
  rewrite ?node_11460.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43959 (s : N.State) (i : N.Inputs) :
  R.v43959 (state s) (inputs i) = Zmod.unsigned (N.v43959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43959 s i)) at 1.
  unfold R.v43959, N.v43959.
  unfold R.v6, N.v6.
  rewrite ?node_11608.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43960 (s : N.State) (i : N.Inputs) :
  R.v43960 (state s) (inputs i) = Zmod.unsigned (N.v43960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43960 s i)) at 1.
  unfold R.v43960, N.v43960.
  unfold R.v6, N.v6.
  rewrite ?node_11660.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43961 (s : N.State) (i : N.Inputs) :
  R.v43961 (state s) (inputs i) = Zmod.unsigned (N.v43961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43961 s i)) at 1.
  unfold R.v43961, N.v43961.
  rewrite ?node_43958.
  rewrite ?node_43959.
  rewrite ?node_43960.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43962 (s : N.State) (i : N.Inputs) :
  R.v43962 (state s) (inputs i) = Zmod.unsigned (N.v43962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43962 s i)) at 1.
  unfold R.v43962, N.v43962.
  rewrite ?node_43957.
  rewrite ?node_43961.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43963 (s : N.State) (i : N.Inputs) :
  R.v43963 (state s) (inputs i) = Zmod.unsigned (N.v43963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43963 s i)) at 1.
  unfold R.v43963, N.v43963.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43964 (s : N.State) (i : N.Inputs) :
  R.v43964 (state s) (inputs i) = Zmod.unsigned (N.v43964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43964 s i)) at 1.
  unfold R.v43964, N.v43964.
  rewrite ?node_11452.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43965 (s : N.State) (i : N.Inputs) :
  R.v43965 (state s) (inputs i) = Zmod.unsigned (N.v43965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43965 s i)) at 1.
  unfold R.v43965, N.v43965.
  unfold R.v6, N.v6.
  rewrite ?node_11444.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43966 (s : N.State) (i : N.Inputs) :
  R.v43966 (state s) (inputs i) = Zmod.unsigned (N.v43966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43966 s i)) at 1.
  unfold R.v43966, N.v43966.
  unfold R.v6, N.v6.
  rewrite ?node_11437.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43967 (s : N.State) (i : N.Inputs) :
  R.v43967 (state s) (inputs i) = Zmod.unsigned (N.v43967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43967 s i)) at 1.
  unfold R.v43967, N.v43967.
  rewrite ?node_43965.
  rewrite ?node_43966.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43968 (s : N.State) (i : N.Inputs) :
  R.v43968 (state s) (inputs i) = Zmod.unsigned (N.v43968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43968 s i)) at 1.
  unfold R.v43968, N.v43968.
  unfold R.v16484, N.v16484.
  rewrite ?node_43967.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43969 (s : N.State) (i : N.Inputs) :
  R.v43969 (state s) (inputs i) = Zmod.unsigned (N.v43969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43969 s i)) at 1.
  unfold R.v43969, N.v43969.
  rewrite ?node_43964.
  rewrite ?node_43968.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43970 (s : N.State) (i : N.Inputs) :
  R.v43970 (state s) (inputs i) = Zmod.unsigned (N.v43970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43970 s i)) at 1.
  unfold R.v43970, N.v43970.
  unfold R.v6, N.v6.
  rewrite ?node_43969.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43971 (s : N.State) (i : N.Inputs) :
  R.v43971 (state s) (inputs i) = Zmod.unsigned (N.v43971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43971 s i)) at 1.
  unfold R.v43971, N.v43971.
  rewrite ?node_11453.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43972 (s : N.State) (i : N.Inputs) :
  R.v43972 (state s) (inputs i) = Zmod.unsigned (N.v43972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43972 s i)) at 1.
  unfold R.v43972, N.v43972.
  unfold R.v6, N.v6.
  rewrite ?node_11608.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43973 (s : N.State) (i : N.Inputs) :
  R.v43973 (state s) (inputs i) = Zmod.unsigned (N.v43973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43973 s i)) at 1.
  unfold R.v43973, N.v43973.
  rewrite ?node_43971.
  rewrite ?node_43972.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43974 (s : N.State) (i : N.Inputs) :
  R.v43974 (state s) (inputs i) = Zmod.unsigned (N.v43974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43974 s i)) at 1.
  unfold R.v43974, N.v43974.
  rewrite ?node_43970.
  rewrite ?node_43973.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43975 (s : N.State) (i : N.Inputs) :
  R.v43975 (state s) (inputs i) = Zmod.unsigned (N.v43975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43975 s i)) at 1.
  unfold R.v43975, N.v43975.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43976 (s : N.State) (i : N.Inputs) :
  R.v43976 (state s) (inputs i) = Zmod.unsigned (N.v43976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43976 s i)) at 1.
  unfold R.v43976, N.v43976.
  rewrite ?node_11459.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43977 (s : N.State) (i : N.Inputs) :
  R.v43977 (state s) (inputs i) = Zmod.unsigned (N.v43977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43977 s i)) at 1.
  unfold R.v43977, N.v43977.
  unfold R.v6, N.v6.
  rewrite ?node_11455.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43978 (s : N.State) (i : N.Inputs) :
  R.v43978 (state s) (inputs i) = Zmod.unsigned (N.v43978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43978 s i)) at 1.
  unfold R.v43978, N.v43978.
  unfold R.v6, N.v6.
  rewrite ?node_11453.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43979 (s : N.State) (i : N.Inputs) :
  R.v43979 (state s) (inputs i) = Zmod.unsigned (N.v43979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43979 s i)) at 1.
  unfold R.v43979, N.v43979.
  rewrite ?node_43977.
  rewrite ?node_43978.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43980 (s : N.State) (i : N.Inputs) :
  R.v43980 (state s) (inputs i) = Zmod.unsigned (N.v43980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43980 s i)) at 1.
  unfold R.v43980, N.v43980.
  unfold R.v16484, N.v16484.
  rewrite ?node_43979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43981 (s : N.State) (i : N.Inputs) :
  R.v43981 (state s) (inputs i) = Zmod.unsigned (N.v43981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43981 s i)) at 1.
  unfold R.v43981, N.v43981.
  rewrite ?node_43976.
  rewrite ?node_43980.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43982 (s : N.State) (i : N.Inputs) :
  R.v43982 (state s) (inputs i) = Zmod.unsigned (N.v43982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43982 s i)) at 1.
  unfold R.v43982, N.v43982.
  unfold R.v6, N.v6.
  rewrite ?node_43981.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43983 (s : N.State) (i : N.Inputs) :
  R.v43983 (state s) (inputs i) = Zmod.unsigned (N.v43983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43983 s i)) at 1.
  unfold R.v43983, N.v43983.
  rewrite ?node_11460.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43984 (s : N.State) (i : N.Inputs) :
  R.v43984 (state s) (inputs i) = Zmod.unsigned (N.v43984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43984 s i)) at 1.
  unfold R.v43984, N.v43984.
  unfold R.v6, N.v6.
  rewrite ?node_11660.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43985 (s : N.State) (i : N.Inputs) :
  R.v43985 (state s) (inputs i) = Zmod.unsigned (N.v43985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43985 s i)) at 1.
  unfold R.v43985, N.v43985.
  rewrite ?node_43983.
  rewrite ?node_43984.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43986 (s : N.State) (i : N.Inputs) :
  R.v43986 (state s) (inputs i) = Zmod.unsigned (N.v43986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43986 s i)) at 1.
  unfold R.v43986, N.v43986.
  rewrite ?node_43982.
  rewrite ?node_43985.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43987 (s : N.State) (i : N.Inputs) :
  R.v43987 (state s) (inputs i) = Zmod.unsigned (N.v43987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43987 s i)) at 1.
  unfold R.v43987, N.v43987.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43988 (s : N.State) (i : N.Inputs) :
  R.v43988 (state s) (inputs i) = Zmod.unsigned (N.v43988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43988 s i)) at 1.
  unfold R.v43988, N.v43988.
  rewrite ?node_11479.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43989 (s : N.State) (i : N.Inputs) :
  R.v43989 (state s) (inputs i) = Zmod.unsigned (N.v43989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43989 s i)) at 1.
  unfold R.v43989, N.v43989.
  rewrite ?node_11475.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43990 (s : N.State) (i : N.Inputs) :
  R.v43990 (state s) (inputs i) = Zmod.unsigned (N.v43990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43990 s i)) at 1.
  unfold R.v43990, N.v43990.
  rewrite ?node_11471.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43991 (s : N.State) (i : N.Inputs) :
  R.v43991 (state s) (inputs i) = Zmod.unsigned (N.v43991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43991 s i)) at 1.
  unfold R.v43991, N.v43991.
  unfold R.v6, N.v6.
  rewrite ?node_11467.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43992 (s : N.State) (i : N.Inputs) :
  R.v43992 (state s) (inputs i) = Zmod.unsigned (N.v43992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43992 s i)) at 1.
  unfold R.v43992, N.v43992.
  unfold R.v6, N.v6.
  rewrite ?node_11464.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43993 (s : N.State) (i : N.Inputs) :
  R.v43993 (state s) (inputs i) = Zmod.unsigned (N.v43993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43993 s i)) at 1.
  unfold R.v43993, N.v43993.
  rewrite ?node_43991.
  rewrite ?node_43992.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43994 (s : N.State) (i : N.Inputs) :
  R.v43994 (state s) (inputs i) = Zmod.unsigned (N.v43994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43994 s i)) at 1.
  unfold R.v43994, N.v43994.
  unfold R.v16484, N.v16484.
  rewrite ?node_43993.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43995 (s : N.State) (i : N.Inputs) :
  R.v43995 (state s) (inputs i) = Zmod.unsigned (N.v43995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43995 s i)) at 1.
  unfold R.v43995, N.v43995.
  rewrite ?node_43988.
  rewrite ?node_43989.
  rewrite ?node_43990.
  rewrite ?node_43994.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43996 (s : N.State) (i : N.Inputs) :
  R.v43996 (state s) (inputs i) = Zmod.unsigned (N.v43996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43996 s i)) at 1.
  unfold R.v43996, N.v43996.
  unfold R.v6, N.v6.
  rewrite ?node_43995.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43997 (s : N.State) (i : N.Inputs) :
  R.v43997 (state s) (inputs i) = Zmod.unsigned (N.v43997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43997 s i)) at 1.
  unfold R.v43997, N.v43997.
  rewrite ?node_11480.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43998 (s : N.State) (i : N.Inputs) :
  R.v43998 (state s) (inputs i) = Zmod.unsigned (N.v43998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43998 s i)) at 1.
  unfold R.v43998, N.v43998.
  unfold R.v6, N.v6.
  rewrite ?node_11628.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_43999 (s : N.State) (i : N.Inputs) :
  R.v43999 (state s) (inputs i) = Zmod.unsigned (N.v43999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v43999 s i)) at 1.
  unfold R.v43999, N.v43999.
  unfold R.v6, N.v6.
  rewrite ?node_11664.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
