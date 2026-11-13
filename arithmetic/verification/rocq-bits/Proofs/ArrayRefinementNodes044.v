(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes043.
Lemma node_44000 (s : N.State) (i : N.Inputs) :
  R.v44000 (state s) (inputs i) = Zmod.unsigned (N.v44000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44000 s i)) at 1.
  unfold R.v44000, N.v44000.
  rewrite ?node_43997.
  rewrite ?node_43998.
  rewrite ?node_43999.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44001 (s : N.State) (i : N.Inputs) :
  R.v44001 (state s) (inputs i) = Zmod.unsigned (N.v44001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44001 s i)) at 1.
  unfold R.v44001, N.v44001.
  rewrite ?node_43996.
  rewrite ?node_44000.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44002 (s : N.State) (i : N.Inputs) :
  R.v44002 (state s) (inputs i) = Zmod.unsigned (N.v44002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44002 s i)) at 1.
  unfold R.v44002, N.v44002.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44003 (s : N.State) (i : N.Inputs) :
  R.v44003 (state s) (inputs i) = Zmod.unsigned (N.v44003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44003 s i)) at 1.
  unfold R.v44003, N.v44003.
  rewrite ?node_11471.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44004 (s : N.State) (i : N.Inputs) :
  R.v44004 (state s) (inputs i) = Zmod.unsigned (N.v44004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44004 s i)) at 1.
  unfold R.v44004, N.v44004.
  unfold R.v6, N.v6.
  rewrite ?node_11467.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44005 (s : N.State) (i : N.Inputs) :
  R.v44005 (state s) (inputs i) = Zmod.unsigned (N.v44005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44005 s i)) at 1.
  unfold R.v44005, N.v44005.
  unfold R.v6, N.v6.
  rewrite ?node_11464.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44006 (s : N.State) (i : N.Inputs) :
  R.v44006 (state s) (inputs i) = Zmod.unsigned (N.v44006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44006 s i)) at 1.
  unfold R.v44006, N.v44006.
  rewrite ?node_44004.
  rewrite ?node_44005.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44007 (s : N.State) (i : N.Inputs) :
  R.v44007 (state s) (inputs i) = Zmod.unsigned (N.v44007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44007 s i)) at 1.
  unfold R.v44007, N.v44007.
  unfold R.v16484, N.v16484.
  rewrite ?node_44006.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44008 (s : N.State) (i : N.Inputs) :
  R.v44008 (state s) (inputs i) = Zmod.unsigned (N.v44008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44008 s i)) at 1.
  unfold R.v44008, N.v44008.
  rewrite ?node_44003.
  rewrite ?node_44007.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44009 (s : N.State) (i : N.Inputs) :
  R.v44009 (state s) (inputs i) = Zmod.unsigned (N.v44009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44009 s i)) at 1.
  unfold R.v44009, N.v44009.
  unfold R.v6, N.v6.
  rewrite ?node_44008.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44010 (s : N.State) (i : N.Inputs) :
  R.v44010 (state s) (inputs i) = Zmod.unsigned (N.v44010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44010 s i)) at 1.
  unfold R.v44010, N.v44010.
  rewrite ?node_11472.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44011 (s : N.State) (i : N.Inputs) :
  R.v44011 (state s) (inputs i) = Zmod.unsigned (N.v44011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44011 s i)) at 1.
  unfold R.v44011, N.v44011.
  unfold R.v6, N.v6.
  rewrite ?node_11628.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44012 (s : N.State) (i : N.Inputs) :
  R.v44012 (state s) (inputs i) = Zmod.unsigned (N.v44012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44012 s i)) at 1.
  unfold R.v44012, N.v44012.
  rewrite ?node_44010.
  rewrite ?node_44011.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44013 (s : N.State) (i : N.Inputs) :
  R.v44013 (state s) (inputs i) = Zmod.unsigned (N.v44013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44013 s i)) at 1.
  unfold R.v44013, N.v44013.
  rewrite ?node_44009.
  rewrite ?node_44012.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44014 (s : N.State) (i : N.Inputs) :
  R.v44014 (state s) (inputs i) = Zmod.unsigned (N.v44014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44014 s i)) at 1.
  unfold R.v44014, N.v44014.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44015 (s : N.State) (i : N.Inputs) :
  R.v44015 (state s) (inputs i) = Zmod.unsigned (N.v44015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44015 s i)) at 1.
  unfold R.v44015, N.v44015.
  rewrite ?node_11479.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44016 (s : N.State) (i : N.Inputs) :
  R.v44016 (state s) (inputs i) = Zmod.unsigned (N.v44016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44016 s i)) at 1.
  unfold R.v44016, N.v44016.
  unfold R.v6, N.v6.
  rewrite ?node_11475.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44017 (s : N.State) (i : N.Inputs) :
  R.v44017 (state s) (inputs i) = Zmod.unsigned (N.v44017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44017 s i)) at 1.
  unfold R.v44017, N.v44017.
  unfold R.v6, N.v6.
  rewrite ?node_11472.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44018 (s : N.State) (i : N.Inputs) :
  R.v44018 (state s) (inputs i) = Zmod.unsigned (N.v44018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44018 s i)) at 1.
  unfold R.v44018, N.v44018.
  rewrite ?node_44016.
  rewrite ?node_44017.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44019 (s : N.State) (i : N.Inputs) :
  R.v44019 (state s) (inputs i) = Zmod.unsigned (N.v44019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44019 s i)) at 1.
  unfold R.v44019, N.v44019.
  unfold R.v16484, N.v16484.
  rewrite ?node_44018.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44020 (s : N.State) (i : N.Inputs) :
  R.v44020 (state s) (inputs i) = Zmod.unsigned (N.v44020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44020 s i)) at 1.
  unfold R.v44020, N.v44020.
  rewrite ?node_44015.
  rewrite ?node_44019.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44021 (s : N.State) (i : N.Inputs) :
  R.v44021 (state s) (inputs i) = Zmod.unsigned (N.v44021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44021 s i)) at 1.
  unfold R.v44021, N.v44021.
  unfold R.v6, N.v6.
  rewrite ?node_44020.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44022 (s : N.State) (i : N.Inputs) :
  R.v44022 (state s) (inputs i) = Zmod.unsigned (N.v44022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44022 s i)) at 1.
  unfold R.v44022, N.v44022.
  rewrite ?node_11480.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44023 (s : N.State) (i : N.Inputs) :
  R.v44023 (state s) (inputs i) = Zmod.unsigned (N.v44023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44023 s i)) at 1.
  unfold R.v44023, N.v44023.
  unfold R.v6, N.v6.
  rewrite ?node_11664.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44024 (s : N.State) (i : N.Inputs) :
  R.v44024 (state s) (inputs i) = Zmod.unsigned (N.v44024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44024 s i)) at 1.
  unfold R.v44024, N.v44024.
  rewrite ?node_44022.
  rewrite ?node_44023.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44025 (s : N.State) (i : N.Inputs) :
  R.v44025 (state s) (inputs i) = Zmod.unsigned (N.v44025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44025 s i)) at 1.
  unfold R.v44025, N.v44025.
  rewrite ?node_44021.
  rewrite ?node_44024.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44026 (s : N.State) (i : N.Inputs) :
  R.v44026 (state s) (inputs i) = Zmod.unsigned (N.v44026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44026 s i)) at 1.
  unfold R.v44026, N.v44026.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44027 (s : N.State) (i : N.Inputs) :
  R.v44027 (state s) (inputs i) = Zmod.unsigned (N.v44027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44027 s i)) at 1.
  unfold R.v44027, N.v44027.
  rewrite ?node_11499.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44028 (s : N.State) (i : N.Inputs) :
  R.v44028 (state s) (inputs i) = Zmod.unsigned (N.v44028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44028 s i)) at 1.
  unfold R.v44028, N.v44028.
  rewrite ?node_11495.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44029 (s : N.State) (i : N.Inputs) :
  R.v44029 (state s) (inputs i) = Zmod.unsigned (N.v44029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44029 s i)) at 1.
  unfold R.v44029, N.v44029.
  rewrite ?node_11491.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44030 (s : N.State) (i : N.Inputs) :
  R.v44030 (state s) (inputs i) = Zmod.unsigned (N.v44030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44030 s i)) at 1.
  unfold R.v44030, N.v44030.
  unfold R.v6, N.v6.
  rewrite ?node_11487.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44031 (s : N.State) (i : N.Inputs) :
  R.v44031 (state s) (inputs i) = Zmod.unsigned (N.v44031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44031 s i)) at 1.
  unfold R.v44031, N.v44031.
  unfold R.v6, N.v6.
  rewrite ?node_11484.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44032 (s : N.State) (i : N.Inputs) :
  R.v44032 (state s) (inputs i) = Zmod.unsigned (N.v44032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44032 s i)) at 1.
  unfold R.v44032, N.v44032.
  rewrite ?node_44030.
  rewrite ?node_44031.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44033 (s : N.State) (i : N.Inputs) :
  R.v44033 (state s) (inputs i) = Zmod.unsigned (N.v44033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44033 s i)) at 1.
  unfold R.v44033, N.v44033.
  unfold R.v16484, N.v16484.
  rewrite ?node_44032.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44034 (s : N.State) (i : N.Inputs) :
  R.v44034 (state s) (inputs i) = Zmod.unsigned (N.v44034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44034 s i)) at 1.
  unfold R.v44034, N.v44034.
  rewrite ?node_44027.
  rewrite ?node_44028.
  rewrite ?node_44029.
  rewrite ?node_44033.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44035 (s : N.State) (i : N.Inputs) :
  R.v44035 (state s) (inputs i) = Zmod.unsigned (N.v44035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44035 s i)) at 1.
  unfold R.v44035, N.v44035.
  unfold R.v6, N.v6.
  rewrite ?node_44034.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44036 (s : N.State) (i : N.Inputs) :
  R.v44036 (state s) (inputs i) = Zmod.unsigned (N.v44036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44036 s i)) at 1.
  unfold R.v44036, N.v44036.
  rewrite ?node_11500.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44037 (s : N.State) (i : N.Inputs) :
  R.v44037 (state s) (inputs i) = Zmod.unsigned (N.v44037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44037 s i)) at 1.
  unfold R.v44037, N.v44037.
  unfold R.v6, N.v6.
  rewrite ?node_11648.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44038 (s : N.State) (i : N.Inputs) :
  R.v44038 (state s) (inputs i) = Zmod.unsigned (N.v44038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44038 s i)) at 1.
  unfold R.v44038, N.v44038.
  unfold R.v6, N.v6.
  rewrite ?node_11668.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44039 (s : N.State) (i : N.Inputs) :
  R.v44039 (state s) (inputs i) = Zmod.unsigned (N.v44039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44039 s i)) at 1.
  unfold R.v44039, N.v44039.
  rewrite ?node_44036.
  rewrite ?node_44037.
  rewrite ?node_44038.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44040 (s : N.State) (i : N.Inputs) :
  R.v44040 (state s) (inputs i) = Zmod.unsigned (N.v44040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44040 s i)) at 1.
  unfold R.v44040, N.v44040.
  rewrite ?node_44035.
  rewrite ?node_44039.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44041 (s : N.State) (i : N.Inputs) :
  R.v44041 (state s) (inputs i) = Zmod.unsigned (N.v44041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44041 s i)) at 1.
  unfold R.v44041, N.v44041.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44042 (s : N.State) (i : N.Inputs) :
  R.v44042 (state s) (inputs i) = Zmod.unsigned (N.v44042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44042 s i)) at 1.
  unfold R.v44042, N.v44042.
  rewrite ?node_11491.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44043 (s : N.State) (i : N.Inputs) :
  R.v44043 (state s) (inputs i) = Zmod.unsigned (N.v44043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44043 s i)) at 1.
  unfold R.v44043, N.v44043.
  unfold R.v6, N.v6.
  rewrite ?node_11487.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44044 (s : N.State) (i : N.Inputs) :
  R.v44044 (state s) (inputs i) = Zmod.unsigned (N.v44044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44044 s i)) at 1.
  unfold R.v44044, N.v44044.
  unfold R.v6, N.v6.
  rewrite ?node_11484.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44045 (s : N.State) (i : N.Inputs) :
  R.v44045 (state s) (inputs i) = Zmod.unsigned (N.v44045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44045 s i)) at 1.
  unfold R.v44045, N.v44045.
  rewrite ?node_44043.
  rewrite ?node_44044.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44046 (s : N.State) (i : N.Inputs) :
  R.v44046 (state s) (inputs i) = Zmod.unsigned (N.v44046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44046 s i)) at 1.
  unfold R.v44046, N.v44046.
  unfold R.v16484, N.v16484.
  rewrite ?node_44045.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44047 (s : N.State) (i : N.Inputs) :
  R.v44047 (state s) (inputs i) = Zmod.unsigned (N.v44047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44047 s i)) at 1.
  unfold R.v44047, N.v44047.
  rewrite ?node_44042.
  rewrite ?node_44046.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44048 (s : N.State) (i : N.Inputs) :
  R.v44048 (state s) (inputs i) = Zmod.unsigned (N.v44048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44048 s i)) at 1.
  unfold R.v44048, N.v44048.
  unfold R.v6, N.v6.
  rewrite ?node_44047.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44049 (s : N.State) (i : N.Inputs) :
  R.v44049 (state s) (inputs i) = Zmod.unsigned (N.v44049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44049 s i)) at 1.
  unfold R.v44049, N.v44049.
  rewrite ?node_11492.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44050 (s : N.State) (i : N.Inputs) :
  R.v44050 (state s) (inputs i) = Zmod.unsigned (N.v44050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44050 s i)) at 1.
  unfold R.v44050, N.v44050.
  unfold R.v6, N.v6.
  rewrite ?node_11648.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44051 (s : N.State) (i : N.Inputs) :
  R.v44051 (state s) (inputs i) = Zmod.unsigned (N.v44051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44051 s i)) at 1.
  unfold R.v44051, N.v44051.
  rewrite ?node_44049.
  rewrite ?node_44050.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44052 (s : N.State) (i : N.Inputs) :
  R.v44052 (state s) (inputs i) = Zmod.unsigned (N.v44052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44052 s i)) at 1.
  unfold R.v44052, N.v44052.
  rewrite ?node_44048.
  rewrite ?node_44051.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44053 (s : N.State) (i : N.Inputs) :
  R.v44053 (state s) (inputs i) = Zmod.unsigned (N.v44053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44053 s i)) at 1.
  unfold R.v44053, N.v44053.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44054 (s : N.State) (i : N.Inputs) :
  R.v44054 (state s) (inputs i) = Zmod.unsigned (N.v44054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44054 s i)) at 1.
  unfold R.v44054, N.v44054.
  rewrite ?node_11499.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44055 (s : N.State) (i : N.Inputs) :
  R.v44055 (state s) (inputs i) = Zmod.unsigned (N.v44055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44055 s i)) at 1.
  unfold R.v44055, N.v44055.
  unfold R.v6, N.v6.
  rewrite ?node_11495.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44056 (s : N.State) (i : N.Inputs) :
  R.v44056 (state s) (inputs i) = Zmod.unsigned (N.v44056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44056 s i)) at 1.
  unfold R.v44056, N.v44056.
  unfold R.v6, N.v6.
  rewrite ?node_11492.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44057 (s : N.State) (i : N.Inputs) :
  R.v44057 (state s) (inputs i) = Zmod.unsigned (N.v44057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44057 s i)) at 1.
  unfold R.v44057, N.v44057.
  rewrite ?node_44055.
  rewrite ?node_44056.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44058 (s : N.State) (i : N.Inputs) :
  R.v44058 (state s) (inputs i) = Zmod.unsigned (N.v44058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44058 s i)) at 1.
  unfold R.v44058, N.v44058.
  unfold R.v16484, N.v16484.
  rewrite ?node_44057.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44059 (s : N.State) (i : N.Inputs) :
  R.v44059 (state s) (inputs i) = Zmod.unsigned (N.v44059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44059 s i)) at 1.
  unfold R.v44059, N.v44059.
  rewrite ?node_44054.
  rewrite ?node_44058.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44060 (s : N.State) (i : N.Inputs) :
  R.v44060 (state s) (inputs i) = Zmod.unsigned (N.v44060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44060 s i)) at 1.
  unfold R.v44060, N.v44060.
  unfold R.v6, N.v6.
  rewrite ?node_44059.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44061 (s : N.State) (i : N.Inputs) :
  R.v44061 (state s) (inputs i) = Zmod.unsigned (N.v44061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44061 s i)) at 1.
  unfold R.v44061, N.v44061.
  rewrite ?node_11500.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44062 (s : N.State) (i : N.Inputs) :
  R.v44062 (state s) (inputs i) = Zmod.unsigned (N.v44062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44062 s i)) at 1.
  unfold R.v44062, N.v44062.
  unfold R.v6, N.v6.
  rewrite ?node_11668.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44063 (s : N.State) (i : N.Inputs) :
  R.v44063 (state s) (inputs i) = Zmod.unsigned (N.v44063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44063 s i)) at 1.
  unfold R.v44063, N.v44063.
  rewrite ?node_44061.
  rewrite ?node_44062.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44064 (s : N.State) (i : N.Inputs) :
  R.v44064 (state s) (inputs i) = Zmod.unsigned (N.v44064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44064 s i)) at 1.
  unfold R.v44064, N.v44064.
  rewrite ?node_44060.
  rewrite ?node_44063.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44065 (s : N.State) (i : N.Inputs) :
  R.v44065 (state s) (inputs i) = Zmod.unsigned (N.v44065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44065 s i)) at 1.
  unfold R.v44065, N.v44065.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44066 (s : N.State) (i : N.Inputs) :
  R.v44066 (state s) (inputs i) = Zmod.unsigned (N.v44066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44066 s i)) at 1.
  unfold R.v44066, N.v44066.
  rewrite ?node_11579.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44067 (s : N.State) (i : N.Inputs) :
  R.v44067 (state s) (inputs i) = Zmod.unsigned (N.v44067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44067 s i)) at 1.
  unfold R.v44067, N.v44067.
  rewrite ?node_11575.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44068 (s : N.State) (i : N.Inputs) :
  R.v44068 (state s) (inputs i) = Zmod.unsigned (N.v44068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44068 s i)) at 1.
  unfold R.v44068, N.v44068.
  rewrite ?node_11567.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44069 (s : N.State) (i : N.Inputs) :
  R.v44069 (state s) (inputs i) = Zmod.unsigned (N.v44069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44069 s i)) at 1.
  unfold R.v44069, N.v44069.
  unfold R.v6, N.v6.
  rewrite ?node_11559.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44070 (s : N.State) (i : N.Inputs) :
  R.v44070 (state s) (inputs i) = Zmod.unsigned (N.v44070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44070 s i)) at 1.
  unfold R.v44070, N.v44070.
  unfold R.v6, N.v6.
  rewrite ?node_11552.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44071 (s : N.State) (i : N.Inputs) :
  R.v44071 (state s) (inputs i) = Zmod.unsigned (N.v44071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44071 s i)) at 1.
  unfold R.v44071, N.v44071.
  rewrite ?node_44069.
  rewrite ?node_44070.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44072 (s : N.State) (i : N.Inputs) :
  R.v44072 (state s) (inputs i) = Zmod.unsigned (N.v44072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44072 s i)) at 1.
  unfold R.v44072, N.v44072.
  unfold R.v16484, N.v16484.
  rewrite ?node_44071.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44073 (s : N.State) (i : N.Inputs) :
  R.v44073 (state s) (inputs i) = Zmod.unsigned (N.v44073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44073 s i)) at 1.
  unfold R.v44073, N.v44073.
  rewrite ?node_44066.
  rewrite ?node_44067.
  rewrite ?node_44068.
  rewrite ?node_44072.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44074 (s : N.State) (i : N.Inputs) :
  R.v44074 (state s) (inputs i) = Zmod.unsigned (N.v44074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44074 s i)) at 1.
  unfold R.v44074, N.v44074.
  unfold R.v6, N.v6.
  rewrite ?node_44073.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44075 (s : N.State) (i : N.Inputs) :
  R.v44075 (state s) (inputs i) = Zmod.unsigned (N.v44075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44075 s i)) at 1.
  unfold R.v44075, N.v44075.
  rewrite ?node_11580.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44076 (s : N.State) (i : N.Inputs) :
  R.v44076 (state s) (inputs i) = Zmod.unsigned (N.v44076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44076 s i)) at 1.
  unfold R.v44076, N.v44076.
  unfold R.v6, N.v6.
  rewrite ?node_11727.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44077 (s : N.State) (i : N.Inputs) :
  R.v44077 (state s) (inputs i) = Zmod.unsigned (N.v44077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44077 s i)) at 1.
  unfold R.v44077, N.v44077.
  unfold R.v6, N.v6.
  rewrite ?node_11803.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44078 (s : N.State) (i : N.Inputs) :
  R.v44078 (state s) (inputs i) = Zmod.unsigned (N.v44078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44078 s i)) at 1.
  unfold R.v44078, N.v44078.
  rewrite ?node_44075.
  rewrite ?node_44076.
  rewrite ?node_44077.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44079 (s : N.State) (i : N.Inputs) :
  R.v44079 (state s) (inputs i) = Zmod.unsigned (N.v44079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44079 s i)) at 1.
  unfold R.v44079, N.v44079.
  rewrite ?node_44074.
  rewrite ?node_44078.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44080 (s : N.State) (i : N.Inputs) :
  R.v44080 (state s) (inputs i) = Zmod.unsigned (N.v44080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44080 s i)) at 1.
  unfold R.v44080, N.v44080.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44081 (s : N.State) (i : N.Inputs) :
  R.v44081 (state s) (inputs i) = Zmod.unsigned (N.v44081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44081 s i)) at 1.
  unfold R.v44081, N.v44081.
  rewrite ?node_11567.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44082 (s : N.State) (i : N.Inputs) :
  R.v44082 (state s) (inputs i) = Zmod.unsigned (N.v44082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44082 s i)) at 1.
  unfold R.v44082, N.v44082.
  unfold R.v6, N.v6.
  rewrite ?node_11559.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44083 (s : N.State) (i : N.Inputs) :
  R.v44083 (state s) (inputs i) = Zmod.unsigned (N.v44083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44083 s i)) at 1.
  unfold R.v44083, N.v44083.
  unfold R.v6, N.v6.
  rewrite ?node_11552.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44084 (s : N.State) (i : N.Inputs) :
  R.v44084 (state s) (inputs i) = Zmod.unsigned (N.v44084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44084 s i)) at 1.
  unfold R.v44084, N.v44084.
  rewrite ?node_44082.
  rewrite ?node_44083.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44085 (s : N.State) (i : N.Inputs) :
  R.v44085 (state s) (inputs i) = Zmod.unsigned (N.v44085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44085 s i)) at 1.
  unfold R.v44085, N.v44085.
  unfold R.v16484, N.v16484.
  rewrite ?node_44084.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44086 (s : N.State) (i : N.Inputs) :
  R.v44086 (state s) (inputs i) = Zmod.unsigned (N.v44086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44086 s i)) at 1.
  unfold R.v44086, N.v44086.
  rewrite ?node_44081.
  rewrite ?node_44085.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44087 (s : N.State) (i : N.Inputs) :
  R.v44087 (state s) (inputs i) = Zmod.unsigned (N.v44087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44087 s i)) at 1.
  unfold R.v44087, N.v44087.
  unfold R.v6, N.v6.
  rewrite ?node_44086.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44088 (s : N.State) (i : N.Inputs) :
  R.v44088 (state s) (inputs i) = Zmod.unsigned (N.v44088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44088 s i)) at 1.
  unfold R.v44088, N.v44088.
  rewrite ?node_11568.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44089 (s : N.State) (i : N.Inputs) :
  R.v44089 (state s) (inputs i) = Zmod.unsigned (N.v44089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44089 s i)) at 1.
  unfold R.v44089, N.v44089.
  unfold R.v6, N.v6.
  rewrite ?node_11727.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44090 (s : N.State) (i : N.Inputs) :
  R.v44090 (state s) (inputs i) = Zmod.unsigned (N.v44090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44090 s i)) at 1.
  unfold R.v44090, N.v44090.
  rewrite ?node_44088.
  rewrite ?node_44089.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44091 (s : N.State) (i : N.Inputs) :
  R.v44091 (state s) (inputs i) = Zmod.unsigned (N.v44091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44091 s i)) at 1.
  unfold R.v44091, N.v44091.
  rewrite ?node_44087.
  rewrite ?node_44090.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44092 (s : N.State) (i : N.Inputs) :
  R.v44092 (state s) (inputs i) = Zmod.unsigned (N.v44092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44092 s i)) at 1.
  unfold R.v44092, N.v44092.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44093 (s : N.State) (i : N.Inputs) :
  R.v44093 (state s) (inputs i) = Zmod.unsigned (N.v44093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44093 s i)) at 1.
  unfold R.v44093, N.v44093.
  rewrite ?node_11579.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44094 (s : N.State) (i : N.Inputs) :
  R.v44094 (state s) (inputs i) = Zmod.unsigned (N.v44094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44094 s i)) at 1.
  unfold R.v44094, N.v44094.
  unfold R.v6, N.v6.
  rewrite ?node_11575.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44095 (s : N.State) (i : N.Inputs) :
  R.v44095 (state s) (inputs i) = Zmod.unsigned (N.v44095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44095 s i)) at 1.
  unfold R.v44095, N.v44095.
  unfold R.v6, N.v6.
  rewrite ?node_11568.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44096 (s : N.State) (i : N.Inputs) :
  R.v44096 (state s) (inputs i) = Zmod.unsigned (N.v44096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44096 s i)) at 1.
  unfold R.v44096, N.v44096.
  rewrite ?node_44094.
  rewrite ?node_44095.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44097 (s : N.State) (i : N.Inputs) :
  R.v44097 (state s) (inputs i) = Zmod.unsigned (N.v44097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44097 s i)) at 1.
  unfold R.v44097, N.v44097.
  unfold R.v16484, N.v16484.
  rewrite ?node_44096.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44098 (s : N.State) (i : N.Inputs) :
  R.v44098 (state s) (inputs i) = Zmod.unsigned (N.v44098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44098 s i)) at 1.
  unfold R.v44098, N.v44098.
  rewrite ?node_44093.
  rewrite ?node_44097.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44099 (s : N.State) (i : N.Inputs) :
  R.v44099 (state s) (inputs i) = Zmod.unsigned (N.v44099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44099 s i)) at 1.
  unfold R.v44099, N.v44099.
  unfold R.v6, N.v6.
  rewrite ?node_44098.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44100 (s : N.State) (i : N.Inputs) :
  R.v44100 (state s) (inputs i) = Zmod.unsigned (N.v44100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44100 s i)) at 1.
  unfold R.v44100, N.v44100.
  rewrite ?node_11580.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44101 (s : N.State) (i : N.Inputs) :
  R.v44101 (state s) (inputs i) = Zmod.unsigned (N.v44101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44101 s i)) at 1.
  unfold R.v44101, N.v44101.
  unfold R.v6, N.v6.
  rewrite ?node_11803.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44102 (s : N.State) (i : N.Inputs) :
  R.v44102 (state s) (inputs i) = Zmod.unsigned (N.v44102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44102 s i)) at 1.
  unfold R.v44102, N.v44102.
  rewrite ?node_44100.
  rewrite ?node_44101.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44103 (s : N.State) (i : N.Inputs) :
  R.v44103 (state s) (inputs i) = Zmod.unsigned (N.v44103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44103 s i)) at 1.
  unfold R.v44103, N.v44103.
  rewrite ?node_44099.
  rewrite ?node_44102.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44104 (s : N.State) (i : N.Inputs) :
  R.v44104 (state s) (inputs i) = Zmod.unsigned (N.v44104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44104 s i)) at 1.
  unfold R.v44104, N.v44104.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44105 (s : N.State) (i : N.Inputs) :
  R.v44105 (state s) (inputs i) = Zmod.unsigned (N.v44105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44105 s i)) at 1.
  unfold R.v44105, N.v44105.
  rewrite ?node_11608.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44106 (s : N.State) (i : N.Inputs) :
  R.v44106 (state s) (inputs i) = Zmod.unsigned (N.v44106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44106 s i)) at 1.
  unfold R.v44106, N.v44106.
  rewrite ?node_11604.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44107 (s : N.State) (i : N.Inputs) :
  R.v44107 (state s) (inputs i) = Zmod.unsigned (N.v44107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44107 s i)) at 1.
  unfold R.v44107, N.v44107.
  rewrite ?node_11602.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44108 (s : N.State) (i : N.Inputs) :
  R.v44108 (state s) (inputs i) = Zmod.unsigned (N.v44108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44108 s i)) at 1.
  unfold R.v44108, N.v44108.
  unfold R.v6, N.v6.
  rewrite ?node_11594.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44109 (s : N.State) (i : N.Inputs) :
  R.v44109 (state s) (inputs i) = Zmod.unsigned (N.v44109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44109 s i)) at 1.
  unfold R.v44109, N.v44109.
  unfold R.v6, N.v6.
  rewrite ?node_11587.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44110 (s : N.State) (i : N.Inputs) :
  R.v44110 (state s) (inputs i) = Zmod.unsigned (N.v44110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44110 s i)) at 1.
  unfold R.v44110, N.v44110.
  rewrite ?node_44108.
  rewrite ?node_44109.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44111 (s : N.State) (i : N.Inputs) :
  R.v44111 (state s) (inputs i) = Zmod.unsigned (N.v44111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44111 s i)) at 1.
  unfold R.v44111, N.v44111.
  unfold R.v16484, N.v16484.
  rewrite ?node_44110.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44112 (s : N.State) (i : N.Inputs) :
  R.v44112 (state s) (inputs i) = Zmod.unsigned (N.v44112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44112 s i)) at 1.
  unfold R.v44112, N.v44112.
  rewrite ?node_44105.
  rewrite ?node_44106.
  rewrite ?node_44107.
  rewrite ?node_44111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44113 (s : N.State) (i : N.Inputs) :
  R.v44113 (state s) (inputs i) = Zmod.unsigned (N.v44113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44113 s i)) at 1.
  unfold R.v44113, N.v44113.
  unfold R.v6, N.v6.
  rewrite ?node_44112.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44114 (s : N.State) (i : N.Inputs) :
  R.v44114 (state s) (inputs i) = Zmod.unsigned (N.v44114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44114 s i)) at 1.
  unfold R.v44114, N.v44114.
  rewrite ?node_11609.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44115 (s : N.State) (i : N.Inputs) :
  R.v44115 (state s) (inputs i) = Zmod.unsigned (N.v44115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44115 s i)) at 1.
  unfold R.v44115, N.v44115.
  unfold R.v6, N.v6.
  rewrite ?node_11756.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44116 (s : N.State) (i : N.Inputs) :
  R.v44116 (state s) (inputs i) = Zmod.unsigned (N.v44116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44116 s i)) at 1.
  unfold R.v44116, N.v44116.
  unfold R.v6, N.v6.
  rewrite ?node_11806.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44117 (s : N.State) (i : N.Inputs) :
  R.v44117 (state s) (inputs i) = Zmod.unsigned (N.v44117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44117 s i)) at 1.
  unfold R.v44117, N.v44117.
  rewrite ?node_44114.
  rewrite ?node_44115.
  rewrite ?node_44116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44118 (s : N.State) (i : N.Inputs) :
  R.v44118 (state s) (inputs i) = Zmod.unsigned (N.v44118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44118 s i)) at 1.
  unfold R.v44118, N.v44118.
  rewrite ?node_44113.
  rewrite ?node_44117.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44119 (s : N.State) (i : N.Inputs) :
  R.v44119 (state s) (inputs i) = Zmod.unsigned (N.v44119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44119 s i)) at 1.
  unfold R.v44119, N.v44119.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44120 (s : N.State) (i : N.Inputs) :
  R.v44120 (state s) (inputs i) = Zmod.unsigned (N.v44120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44120 s i)) at 1.
  unfold R.v44120, N.v44120.
  rewrite ?node_11602.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44121 (s : N.State) (i : N.Inputs) :
  R.v44121 (state s) (inputs i) = Zmod.unsigned (N.v44121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44121 s i)) at 1.
  unfold R.v44121, N.v44121.
  unfold R.v6, N.v6.
  rewrite ?node_11594.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44122 (s : N.State) (i : N.Inputs) :
  R.v44122 (state s) (inputs i) = Zmod.unsigned (N.v44122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44122 s i)) at 1.
  unfold R.v44122, N.v44122.
  unfold R.v6, N.v6.
  rewrite ?node_11587.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44123 (s : N.State) (i : N.Inputs) :
  R.v44123 (state s) (inputs i) = Zmod.unsigned (N.v44123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44123 s i)) at 1.
  unfold R.v44123, N.v44123.
  rewrite ?node_44121.
  rewrite ?node_44122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44124 (s : N.State) (i : N.Inputs) :
  R.v44124 (state s) (inputs i) = Zmod.unsigned (N.v44124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44124 s i)) at 1.
  unfold R.v44124, N.v44124.
  unfold R.v16484, N.v16484.
  rewrite ?node_44123.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44125 (s : N.State) (i : N.Inputs) :
  R.v44125 (state s) (inputs i) = Zmod.unsigned (N.v44125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44125 s i)) at 1.
  unfold R.v44125, N.v44125.
  rewrite ?node_44120.
  rewrite ?node_44124.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44126 (s : N.State) (i : N.Inputs) :
  R.v44126 (state s) (inputs i) = Zmod.unsigned (N.v44126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44126 s i)) at 1.
  unfold R.v44126, N.v44126.
  unfold R.v6, N.v6.
  rewrite ?node_44125.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44127 (s : N.State) (i : N.Inputs) :
  R.v44127 (state s) (inputs i) = Zmod.unsigned (N.v44127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44127 s i)) at 1.
  unfold R.v44127, N.v44127.
  rewrite ?node_11603.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44128 (s : N.State) (i : N.Inputs) :
  R.v44128 (state s) (inputs i) = Zmod.unsigned (N.v44128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44128 s i)) at 1.
  unfold R.v44128, N.v44128.
  unfold R.v6, N.v6.
  rewrite ?node_11756.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44129 (s : N.State) (i : N.Inputs) :
  R.v44129 (state s) (inputs i) = Zmod.unsigned (N.v44129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44129 s i)) at 1.
  unfold R.v44129, N.v44129.
  rewrite ?node_44127.
  rewrite ?node_44128.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44130 (s : N.State) (i : N.Inputs) :
  R.v44130 (state s) (inputs i) = Zmod.unsigned (N.v44130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44130 s i)) at 1.
  unfold R.v44130, N.v44130.
  rewrite ?node_44126.
  rewrite ?node_44129.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44131 (s : N.State) (i : N.Inputs) :
  R.v44131 (state s) (inputs i) = Zmod.unsigned (N.v44131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44131 s i)) at 1.
  unfold R.v44131, N.v44131.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44132 (s : N.State) (i : N.Inputs) :
  R.v44132 (state s) (inputs i) = Zmod.unsigned (N.v44132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44132 s i)) at 1.
  unfold R.v44132, N.v44132.
  rewrite ?node_11608.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44133 (s : N.State) (i : N.Inputs) :
  R.v44133 (state s) (inputs i) = Zmod.unsigned (N.v44133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44133 s i)) at 1.
  unfold R.v44133, N.v44133.
  unfold R.v6, N.v6.
  rewrite ?node_11604.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44134 (s : N.State) (i : N.Inputs) :
  R.v44134 (state s) (inputs i) = Zmod.unsigned (N.v44134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44134 s i)) at 1.
  unfold R.v44134, N.v44134.
  unfold R.v6, N.v6.
  rewrite ?node_11603.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44135 (s : N.State) (i : N.Inputs) :
  R.v44135 (state s) (inputs i) = Zmod.unsigned (N.v44135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44135 s i)) at 1.
  unfold R.v44135, N.v44135.
  rewrite ?node_44133.
  rewrite ?node_44134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44136 (s : N.State) (i : N.Inputs) :
  R.v44136 (state s) (inputs i) = Zmod.unsigned (N.v44136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44136 s i)) at 1.
  unfold R.v44136, N.v44136.
  unfold R.v16484, N.v16484.
  rewrite ?node_44135.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44137 (s : N.State) (i : N.Inputs) :
  R.v44137 (state s) (inputs i) = Zmod.unsigned (N.v44137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44137 s i)) at 1.
  unfold R.v44137, N.v44137.
  rewrite ?node_44132.
  rewrite ?node_44136.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44138 (s : N.State) (i : N.Inputs) :
  R.v44138 (state s) (inputs i) = Zmod.unsigned (N.v44138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44138 s i)) at 1.
  unfold R.v44138, N.v44138.
  unfold R.v6, N.v6.
  rewrite ?node_44137.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44139 (s : N.State) (i : N.Inputs) :
  R.v44139 (state s) (inputs i) = Zmod.unsigned (N.v44139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44139 s i)) at 1.
  unfold R.v44139, N.v44139.
  rewrite ?node_11609.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44140 (s : N.State) (i : N.Inputs) :
  R.v44140 (state s) (inputs i) = Zmod.unsigned (N.v44140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44140 s i)) at 1.
  unfold R.v44140, N.v44140.
  unfold R.v6, N.v6.
  rewrite ?node_11806.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44141 (s : N.State) (i : N.Inputs) :
  R.v44141 (state s) (inputs i) = Zmod.unsigned (N.v44141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44141 s i)) at 1.
  unfold R.v44141, N.v44141.
  rewrite ?node_44139.
  rewrite ?node_44140.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44142 (s : N.State) (i : N.Inputs) :
  R.v44142 (state s) (inputs i) = Zmod.unsigned (N.v44142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44142 s i)) at 1.
  unfold R.v44142, N.v44142.
  rewrite ?node_44138.
  rewrite ?node_44141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44143 (s : N.State) (i : N.Inputs) :
  R.v44143 (state s) (inputs i) = Zmod.unsigned (N.v44143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44143 s i)) at 1.
  unfold R.v44143, N.v44143.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44144 (s : N.State) (i : N.Inputs) :
  R.v44144 (state s) (inputs i) = Zmod.unsigned (N.v44144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44144 s i)) at 1.
  unfold R.v44144, N.v44144.
  rewrite ?node_11628.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44145 (s : N.State) (i : N.Inputs) :
  R.v44145 (state s) (inputs i) = Zmod.unsigned (N.v44145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44145 s i)) at 1.
  unfold R.v44145, N.v44145.
  rewrite ?node_11624.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44146 (s : N.State) (i : N.Inputs) :
  R.v44146 (state s) (inputs i) = Zmod.unsigned (N.v44146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44146 s i)) at 1.
  unfold R.v44146, N.v44146.
  rewrite ?node_11620.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44147 (s : N.State) (i : N.Inputs) :
  R.v44147 (state s) (inputs i) = Zmod.unsigned (N.v44147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44147 s i)) at 1.
  unfold R.v44147, N.v44147.
  unfold R.v6, N.v6.
  rewrite ?node_11616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44148 (s : N.State) (i : N.Inputs) :
  R.v44148 (state s) (inputs i) = Zmod.unsigned (N.v44148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44148 s i)) at 1.
  unfold R.v44148, N.v44148.
  unfold R.v6, N.v6.
  rewrite ?node_11613.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44149 (s : N.State) (i : N.Inputs) :
  R.v44149 (state s) (inputs i) = Zmod.unsigned (N.v44149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44149 s i)) at 1.
  unfold R.v44149, N.v44149.
  rewrite ?node_44147.
  rewrite ?node_44148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44150 (s : N.State) (i : N.Inputs) :
  R.v44150 (state s) (inputs i) = Zmod.unsigned (N.v44150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44150 s i)) at 1.
  unfold R.v44150, N.v44150.
  unfold R.v16484, N.v16484.
  rewrite ?node_44149.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44151 (s : N.State) (i : N.Inputs) :
  R.v44151 (state s) (inputs i) = Zmod.unsigned (N.v44151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44151 s i)) at 1.
  unfold R.v44151, N.v44151.
  rewrite ?node_44144.
  rewrite ?node_44145.
  rewrite ?node_44146.
  rewrite ?node_44150.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44152 (s : N.State) (i : N.Inputs) :
  R.v44152 (state s) (inputs i) = Zmod.unsigned (N.v44152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44152 s i)) at 1.
  unfold R.v44152, N.v44152.
  unfold R.v6, N.v6.
  rewrite ?node_44151.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44153 (s : N.State) (i : N.Inputs) :
  R.v44153 (state s) (inputs i) = Zmod.unsigned (N.v44153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44153 s i)) at 1.
  unfold R.v44153, N.v44153.
  rewrite ?node_11629.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44154 (s : N.State) (i : N.Inputs) :
  R.v44154 (state s) (inputs i) = Zmod.unsigned (N.v44154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44154 s i)) at 1.
  unfold R.v44154, N.v44154.
  unfold R.v6, N.v6.
  rewrite ?node_11776.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44155 (s : N.State) (i : N.Inputs) :
  R.v44155 (state s) (inputs i) = Zmod.unsigned (N.v44155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44155 s i)) at 1.
  unfold R.v44155, N.v44155.
  unfold R.v6, N.v6.
  rewrite ?node_11810.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44156 (s : N.State) (i : N.Inputs) :
  R.v44156 (state s) (inputs i) = Zmod.unsigned (N.v44156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44156 s i)) at 1.
  unfold R.v44156, N.v44156.
  rewrite ?node_44153.
  rewrite ?node_44154.
  rewrite ?node_44155.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44157 (s : N.State) (i : N.Inputs) :
  R.v44157 (state s) (inputs i) = Zmod.unsigned (N.v44157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44157 s i)) at 1.
  unfold R.v44157, N.v44157.
  rewrite ?node_44152.
  rewrite ?node_44156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44158 (s : N.State) (i : N.Inputs) :
  R.v44158 (state s) (inputs i) = Zmod.unsigned (N.v44158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44158 s i)) at 1.
  unfold R.v44158, N.v44158.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44159 (s : N.State) (i : N.Inputs) :
  R.v44159 (state s) (inputs i) = Zmod.unsigned (N.v44159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44159 s i)) at 1.
  unfold R.v44159, N.v44159.
  rewrite ?node_11620.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44160 (s : N.State) (i : N.Inputs) :
  R.v44160 (state s) (inputs i) = Zmod.unsigned (N.v44160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44160 s i)) at 1.
  unfold R.v44160, N.v44160.
  unfold R.v6, N.v6.
  rewrite ?node_11616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44161 (s : N.State) (i : N.Inputs) :
  R.v44161 (state s) (inputs i) = Zmod.unsigned (N.v44161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44161 s i)) at 1.
  unfold R.v44161, N.v44161.
  unfold R.v6, N.v6.
  rewrite ?node_11613.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44162 (s : N.State) (i : N.Inputs) :
  R.v44162 (state s) (inputs i) = Zmod.unsigned (N.v44162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44162 s i)) at 1.
  unfold R.v44162, N.v44162.
  rewrite ?node_44160.
  rewrite ?node_44161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44163 (s : N.State) (i : N.Inputs) :
  R.v44163 (state s) (inputs i) = Zmod.unsigned (N.v44163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44163 s i)) at 1.
  unfold R.v44163, N.v44163.
  unfold R.v16484, N.v16484.
  rewrite ?node_44162.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44164 (s : N.State) (i : N.Inputs) :
  R.v44164 (state s) (inputs i) = Zmod.unsigned (N.v44164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44164 s i)) at 1.
  unfold R.v44164, N.v44164.
  rewrite ?node_44159.
  rewrite ?node_44163.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44165 (s : N.State) (i : N.Inputs) :
  R.v44165 (state s) (inputs i) = Zmod.unsigned (N.v44165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44165 s i)) at 1.
  unfold R.v44165, N.v44165.
  unfold R.v6, N.v6.
  rewrite ?node_44164.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44166 (s : N.State) (i : N.Inputs) :
  R.v44166 (state s) (inputs i) = Zmod.unsigned (N.v44166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44166 s i)) at 1.
  unfold R.v44166, N.v44166.
  rewrite ?node_11621.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44167 (s : N.State) (i : N.Inputs) :
  R.v44167 (state s) (inputs i) = Zmod.unsigned (N.v44167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44167 s i)) at 1.
  unfold R.v44167, N.v44167.
  unfold R.v6, N.v6.
  rewrite ?node_11776.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44168 (s : N.State) (i : N.Inputs) :
  R.v44168 (state s) (inputs i) = Zmod.unsigned (N.v44168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44168 s i)) at 1.
  unfold R.v44168, N.v44168.
  rewrite ?node_44166.
  rewrite ?node_44167.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44169 (s : N.State) (i : N.Inputs) :
  R.v44169 (state s) (inputs i) = Zmod.unsigned (N.v44169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44169 s i)) at 1.
  unfold R.v44169, N.v44169.
  rewrite ?node_44165.
  rewrite ?node_44168.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44170 (s : N.State) (i : N.Inputs) :
  R.v44170 (state s) (inputs i) = Zmod.unsigned (N.v44170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44170 s i)) at 1.
  unfold R.v44170, N.v44170.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44171 (s : N.State) (i : N.Inputs) :
  R.v44171 (state s) (inputs i) = Zmod.unsigned (N.v44171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44171 s i)) at 1.
  unfold R.v44171, N.v44171.
  rewrite ?node_11628.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44172 (s : N.State) (i : N.Inputs) :
  R.v44172 (state s) (inputs i) = Zmod.unsigned (N.v44172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44172 s i)) at 1.
  unfold R.v44172, N.v44172.
  unfold R.v6, N.v6.
  rewrite ?node_11624.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44173 (s : N.State) (i : N.Inputs) :
  R.v44173 (state s) (inputs i) = Zmod.unsigned (N.v44173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44173 s i)) at 1.
  unfold R.v44173, N.v44173.
  unfold R.v6, N.v6.
  rewrite ?node_11621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44174 (s : N.State) (i : N.Inputs) :
  R.v44174 (state s) (inputs i) = Zmod.unsigned (N.v44174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44174 s i)) at 1.
  unfold R.v44174, N.v44174.
  rewrite ?node_44172.
  rewrite ?node_44173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44175 (s : N.State) (i : N.Inputs) :
  R.v44175 (state s) (inputs i) = Zmod.unsigned (N.v44175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44175 s i)) at 1.
  unfold R.v44175, N.v44175.
  unfold R.v16484, N.v16484.
  rewrite ?node_44174.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44176 (s : N.State) (i : N.Inputs) :
  R.v44176 (state s) (inputs i) = Zmod.unsigned (N.v44176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44176 s i)) at 1.
  unfold R.v44176, N.v44176.
  rewrite ?node_44171.
  rewrite ?node_44175.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44177 (s : N.State) (i : N.Inputs) :
  R.v44177 (state s) (inputs i) = Zmod.unsigned (N.v44177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44177 s i)) at 1.
  unfold R.v44177, N.v44177.
  unfold R.v6, N.v6.
  rewrite ?node_44176.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44178 (s : N.State) (i : N.Inputs) :
  R.v44178 (state s) (inputs i) = Zmod.unsigned (N.v44178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44178 s i)) at 1.
  unfold R.v44178, N.v44178.
  rewrite ?node_11629.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44179 (s : N.State) (i : N.Inputs) :
  R.v44179 (state s) (inputs i) = Zmod.unsigned (N.v44179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44179 s i)) at 1.
  unfold R.v44179, N.v44179.
  unfold R.v6, N.v6.
  rewrite ?node_11810.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44180 (s : N.State) (i : N.Inputs) :
  R.v44180 (state s) (inputs i) = Zmod.unsigned (N.v44180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44180 s i)) at 1.
  unfold R.v44180, N.v44180.
  rewrite ?node_44178.
  rewrite ?node_44179.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44181 (s : N.State) (i : N.Inputs) :
  R.v44181 (state s) (inputs i) = Zmod.unsigned (N.v44181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44181 s i)) at 1.
  unfold R.v44181, N.v44181.
  rewrite ?node_44177.
  rewrite ?node_44180.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44182 (s : N.State) (i : N.Inputs) :
  R.v44182 (state s) (inputs i) = Zmod.unsigned (N.v44182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44182 s i)) at 1.
  unfold R.v44182, N.v44182.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44183 (s : N.State) (i : N.Inputs) :
  R.v44183 (state s) (inputs i) = Zmod.unsigned (N.v44183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44183 s i)) at 1.
  unfold R.v44183, N.v44183.
  rewrite ?node_11648.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44184 (s : N.State) (i : N.Inputs) :
  R.v44184 (state s) (inputs i) = Zmod.unsigned (N.v44184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44184 s i)) at 1.
  unfold R.v44184, N.v44184.
  rewrite ?node_11644.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44185 (s : N.State) (i : N.Inputs) :
  R.v44185 (state s) (inputs i) = Zmod.unsigned (N.v44185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44185 s i)) at 1.
  unfold R.v44185, N.v44185.
  rewrite ?node_11640.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44186 (s : N.State) (i : N.Inputs) :
  R.v44186 (state s) (inputs i) = Zmod.unsigned (N.v44186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44186 s i)) at 1.
  unfold R.v44186, N.v44186.
  unfold R.v6, N.v6.
  rewrite ?node_11636.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44187 (s : N.State) (i : N.Inputs) :
  R.v44187 (state s) (inputs i) = Zmod.unsigned (N.v44187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44187 s i)) at 1.
  unfold R.v44187, N.v44187.
  unfold R.v6, N.v6.
  rewrite ?node_11633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44188 (s : N.State) (i : N.Inputs) :
  R.v44188 (state s) (inputs i) = Zmod.unsigned (N.v44188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44188 s i)) at 1.
  unfold R.v44188, N.v44188.
  rewrite ?node_44186.
  rewrite ?node_44187.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44189 (s : N.State) (i : N.Inputs) :
  R.v44189 (state s) (inputs i) = Zmod.unsigned (N.v44189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44189 s i)) at 1.
  unfold R.v44189, N.v44189.
  unfold R.v16484, N.v16484.
  rewrite ?node_44188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44190 (s : N.State) (i : N.Inputs) :
  R.v44190 (state s) (inputs i) = Zmod.unsigned (N.v44190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44190 s i)) at 1.
  unfold R.v44190, N.v44190.
  rewrite ?node_44183.
  rewrite ?node_44184.
  rewrite ?node_44185.
  rewrite ?node_44189.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44191 (s : N.State) (i : N.Inputs) :
  R.v44191 (state s) (inputs i) = Zmod.unsigned (N.v44191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44191 s i)) at 1.
  unfold R.v44191, N.v44191.
  unfold R.v6, N.v6.
  rewrite ?node_44190.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44192 (s : N.State) (i : N.Inputs) :
  R.v44192 (state s) (inputs i) = Zmod.unsigned (N.v44192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44192 s i)) at 1.
  unfold R.v44192, N.v44192.
  rewrite ?node_11649.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44193 (s : N.State) (i : N.Inputs) :
  R.v44193 (state s) (inputs i) = Zmod.unsigned (N.v44193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44193 s i)) at 1.
  unfold R.v44193, N.v44193.
  unfold R.v6, N.v6.
  rewrite ?node_11794.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44194 (s : N.State) (i : N.Inputs) :
  R.v44194 (state s) (inputs i) = Zmod.unsigned (N.v44194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44194 s i)) at 1.
  unfold R.v44194, N.v44194.
  unfold R.v6, N.v6.
  rewrite ?node_11814.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44195 (s : N.State) (i : N.Inputs) :
  R.v44195 (state s) (inputs i) = Zmod.unsigned (N.v44195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44195 s i)) at 1.
  unfold R.v44195, N.v44195.
  rewrite ?node_44192.
  rewrite ?node_44193.
  rewrite ?node_44194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44196 (s : N.State) (i : N.Inputs) :
  R.v44196 (state s) (inputs i) = Zmod.unsigned (N.v44196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44196 s i)) at 1.
  unfold R.v44196, N.v44196.
  rewrite ?node_44191.
  rewrite ?node_44195.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44197 (s : N.State) (i : N.Inputs) :
  R.v44197 (state s) (inputs i) = Zmod.unsigned (N.v44197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44197 s i)) at 1.
  unfold R.v44197, N.v44197.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44198 (s : N.State) (i : N.Inputs) :
  R.v44198 (state s) (inputs i) = Zmod.unsigned (N.v44198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44198 s i)) at 1.
  unfold R.v44198, N.v44198.
  rewrite ?node_11640.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44199 (s : N.State) (i : N.Inputs) :
  R.v44199 (state s) (inputs i) = Zmod.unsigned (N.v44199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44199 s i)) at 1.
  unfold R.v44199, N.v44199.
  unfold R.v6, N.v6.
  rewrite ?node_11636.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44200 (s : N.State) (i : N.Inputs) :
  R.v44200 (state s) (inputs i) = Zmod.unsigned (N.v44200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44200 s i)) at 1.
  unfold R.v44200, N.v44200.
  unfold R.v6, N.v6.
  rewrite ?node_11633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44201 (s : N.State) (i : N.Inputs) :
  R.v44201 (state s) (inputs i) = Zmod.unsigned (N.v44201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44201 s i)) at 1.
  unfold R.v44201, N.v44201.
  rewrite ?node_44199.
  rewrite ?node_44200.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44202 (s : N.State) (i : N.Inputs) :
  R.v44202 (state s) (inputs i) = Zmod.unsigned (N.v44202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44202 s i)) at 1.
  unfold R.v44202, N.v44202.
  unfold R.v16484, N.v16484.
  rewrite ?node_44201.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44203 (s : N.State) (i : N.Inputs) :
  R.v44203 (state s) (inputs i) = Zmod.unsigned (N.v44203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44203 s i)) at 1.
  unfold R.v44203, N.v44203.
  rewrite ?node_44198.
  rewrite ?node_44202.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44204 (s : N.State) (i : N.Inputs) :
  R.v44204 (state s) (inputs i) = Zmod.unsigned (N.v44204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44204 s i)) at 1.
  unfold R.v44204, N.v44204.
  unfold R.v6, N.v6.
  rewrite ?node_44203.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44205 (s : N.State) (i : N.Inputs) :
  R.v44205 (state s) (inputs i) = Zmod.unsigned (N.v44205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44205 s i)) at 1.
  unfold R.v44205, N.v44205.
  rewrite ?node_11641.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44206 (s : N.State) (i : N.Inputs) :
  R.v44206 (state s) (inputs i) = Zmod.unsigned (N.v44206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44206 s i)) at 1.
  unfold R.v44206, N.v44206.
  unfold R.v6, N.v6.
  rewrite ?node_11794.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44207 (s : N.State) (i : N.Inputs) :
  R.v44207 (state s) (inputs i) = Zmod.unsigned (N.v44207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44207 s i)) at 1.
  unfold R.v44207, N.v44207.
  rewrite ?node_44205.
  rewrite ?node_44206.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44208 (s : N.State) (i : N.Inputs) :
  R.v44208 (state s) (inputs i) = Zmod.unsigned (N.v44208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44208 s i)) at 1.
  unfold R.v44208, N.v44208.
  rewrite ?node_44204.
  rewrite ?node_44207.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44209 (s : N.State) (i : N.Inputs) :
  R.v44209 (state s) (inputs i) = Zmod.unsigned (N.v44209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44209 s i)) at 1.
  unfold R.v44209, N.v44209.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44210 (s : N.State) (i : N.Inputs) :
  R.v44210 (state s) (inputs i) = Zmod.unsigned (N.v44210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44210 s i)) at 1.
  unfold R.v44210, N.v44210.
  rewrite ?node_11648.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44211 (s : N.State) (i : N.Inputs) :
  R.v44211 (state s) (inputs i) = Zmod.unsigned (N.v44211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44211 s i)) at 1.
  unfold R.v44211, N.v44211.
  unfold R.v6, N.v6.
  rewrite ?node_11644.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44212 (s : N.State) (i : N.Inputs) :
  R.v44212 (state s) (inputs i) = Zmod.unsigned (N.v44212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44212 s i)) at 1.
  unfold R.v44212, N.v44212.
  unfold R.v6, N.v6.
  rewrite ?node_11641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44213 (s : N.State) (i : N.Inputs) :
  R.v44213 (state s) (inputs i) = Zmod.unsigned (N.v44213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44213 s i)) at 1.
  unfold R.v44213, N.v44213.
  rewrite ?node_44211.
  rewrite ?node_44212.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44214 (s : N.State) (i : N.Inputs) :
  R.v44214 (state s) (inputs i) = Zmod.unsigned (N.v44214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44214 s i)) at 1.
  unfold R.v44214, N.v44214.
  unfold R.v16484, N.v16484.
  rewrite ?node_44213.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44215 (s : N.State) (i : N.Inputs) :
  R.v44215 (state s) (inputs i) = Zmod.unsigned (N.v44215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44215 s i)) at 1.
  unfold R.v44215, N.v44215.
  rewrite ?node_44210.
  rewrite ?node_44214.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44216 (s : N.State) (i : N.Inputs) :
  R.v44216 (state s) (inputs i) = Zmod.unsigned (N.v44216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44216 s i)) at 1.
  unfold R.v44216, N.v44216.
  unfold R.v6, N.v6.
  rewrite ?node_44215.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44217 (s : N.State) (i : N.Inputs) :
  R.v44217 (state s) (inputs i) = Zmod.unsigned (N.v44217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44217 s i)) at 1.
  unfold R.v44217, N.v44217.
  rewrite ?node_11649.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44218 (s : N.State) (i : N.Inputs) :
  R.v44218 (state s) (inputs i) = Zmod.unsigned (N.v44218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44218 s i)) at 1.
  unfold R.v44218, N.v44218.
  unfold R.v6, N.v6.
  rewrite ?node_11814.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44219 (s : N.State) (i : N.Inputs) :
  R.v44219 (state s) (inputs i) = Zmod.unsigned (N.v44219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44219 s i)) at 1.
  unfold R.v44219, N.v44219.
  rewrite ?node_44217.
  rewrite ?node_44218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44220 (s : N.State) (i : N.Inputs) :
  R.v44220 (state s) (inputs i) = Zmod.unsigned (N.v44220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44220 s i)) at 1.
  unfold R.v44220, N.v44220.
  rewrite ?node_44216.
  rewrite ?node_44219.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44221 (s : N.State) (i : N.Inputs) :
  R.v44221 (state s) (inputs i) = Zmod.unsigned (N.v44221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44221 s i)) at 1.
  unfold R.v44221, N.v44221.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44222 (s : N.State) (i : N.Inputs) :
  R.v44222 (state s) (inputs i) = Zmod.unsigned (N.v44222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44222 s i)) at 1.
  unfold R.v44222, N.v44222.
  rewrite ?node_11727.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44223 (s : N.State) (i : N.Inputs) :
  R.v44223 (state s) (inputs i) = Zmod.unsigned (N.v44223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44223 s i)) at 1.
  unfold R.v44223, N.v44223.
  rewrite ?node_11723.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44224 (s : N.State) (i : N.Inputs) :
  R.v44224 (state s) (inputs i) = Zmod.unsigned (N.v44224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44224 s i)) at 1.
  unfold R.v44224, N.v44224.
  rewrite ?node_11715.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44225 (s : N.State) (i : N.Inputs) :
  R.v44225 (state s) (inputs i) = Zmod.unsigned (N.v44225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44225 s i)) at 1.
  unfold R.v44225, N.v44225.
  unfold R.v6, N.v6.
  rewrite ?node_11707.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44226 (s : N.State) (i : N.Inputs) :
  R.v44226 (state s) (inputs i) = Zmod.unsigned (N.v44226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44226 s i)) at 1.
  unfold R.v44226, N.v44226.
  unfold R.v6, N.v6.
  rewrite ?node_11700.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44227 (s : N.State) (i : N.Inputs) :
  R.v44227 (state s) (inputs i) = Zmod.unsigned (N.v44227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44227 s i)) at 1.
  unfold R.v44227, N.v44227.
  rewrite ?node_44225.
  rewrite ?node_44226.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44228 (s : N.State) (i : N.Inputs) :
  R.v44228 (state s) (inputs i) = Zmod.unsigned (N.v44228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44228 s i)) at 1.
  unfold R.v44228, N.v44228.
  unfold R.v16484, N.v16484.
  rewrite ?node_44227.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44229 (s : N.State) (i : N.Inputs) :
  R.v44229 (state s) (inputs i) = Zmod.unsigned (N.v44229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44229 s i)) at 1.
  unfold R.v44229, N.v44229.
  rewrite ?node_44222.
  rewrite ?node_44223.
  rewrite ?node_44224.
  rewrite ?node_44228.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44230 (s : N.State) (i : N.Inputs) :
  R.v44230 (state s) (inputs i) = Zmod.unsigned (N.v44230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44230 s i)) at 1.
  unfold R.v44230, N.v44230.
  unfold R.v6, N.v6.
  rewrite ?node_44229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44231 (s : N.State) (i : N.Inputs) :
  R.v44231 (state s) (inputs i) = Zmod.unsigned (N.v44231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44231 s i)) at 1.
  unfold R.v44231, N.v44231.
  rewrite ?node_11728.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44232 (s : N.State) (i : N.Inputs) :
  R.v44232 (state s) (inputs i) = Zmod.unsigned (N.v44232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44232 s i)) at 1.
  unfold R.v44232, N.v44232.
  unfold R.v6, N.v6.
  rewrite ?node_11872.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44233 (s : N.State) (i : N.Inputs) :
  R.v44233 (state s) (inputs i) = Zmod.unsigned (N.v44233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44233 s i)) at 1.
  unfold R.v44233, N.v44233.
  unfold R.v6, N.v6.
  rewrite ?node_11947.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44234 (s : N.State) (i : N.Inputs) :
  R.v44234 (state s) (inputs i) = Zmod.unsigned (N.v44234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44234 s i)) at 1.
  unfold R.v44234, N.v44234.
  rewrite ?node_44231.
  rewrite ?node_44232.
  rewrite ?node_44233.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44235 (s : N.State) (i : N.Inputs) :
  R.v44235 (state s) (inputs i) = Zmod.unsigned (N.v44235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44235 s i)) at 1.
  unfold R.v44235, N.v44235.
  rewrite ?node_44230.
  rewrite ?node_44234.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44236 (s : N.State) (i : N.Inputs) :
  R.v44236 (state s) (inputs i) = Zmod.unsigned (N.v44236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44236 s i)) at 1.
  unfold R.v44236, N.v44236.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44237 (s : N.State) (i : N.Inputs) :
  R.v44237 (state s) (inputs i) = Zmod.unsigned (N.v44237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44237 s i)) at 1.
  unfold R.v44237, N.v44237.
  rewrite ?node_11715.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44238 (s : N.State) (i : N.Inputs) :
  R.v44238 (state s) (inputs i) = Zmod.unsigned (N.v44238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44238 s i)) at 1.
  unfold R.v44238, N.v44238.
  unfold R.v6, N.v6.
  rewrite ?node_11707.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44239 (s : N.State) (i : N.Inputs) :
  R.v44239 (state s) (inputs i) = Zmod.unsigned (N.v44239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44239 s i)) at 1.
  unfold R.v44239, N.v44239.
  unfold R.v6, N.v6.
  rewrite ?node_11700.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44240 (s : N.State) (i : N.Inputs) :
  R.v44240 (state s) (inputs i) = Zmod.unsigned (N.v44240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44240 s i)) at 1.
  unfold R.v44240, N.v44240.
  rewrite ?node_44238.
  rewrite ?node_44239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44241 (s : N.State) (i : N.Inputs) :
  R.v44241 (state s) (inputs i) = Zmod.unsigned (N.v44241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44241 s i)) at 1.
  unfold R.v44241, N.v44241.
  unfold R.v16484, N.v16484.
  rewrite ?node_44240.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44242 (s : N.State) (i : N.Inputs) :
  R.v44242 (state s) (inputs i) = Zmod.unsigned (N.v44242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44242 s i)) at 1.
  unfold R.v44242, N.v44242.
  rewrite ?node_44237.
  rewrite ?node_44241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44243 (s : N.State) (i : N.Inputs) :
  R.v44243 (state s) (inputs i) = Zmod.unsigned (N.v44243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44243 s i)) at 1.
  unfold R.v44243, N.v44243.
  unfold R.v6, N.v6.
  rewrite ?node_44242.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44244 (s : N.State) (i : N.Inputs) :
  R.v44244 (state s) (inputs i) = Zmod.unsigned (N.v44244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44244 s i)) at 1.
  unfold R.v44244, N.v44244.
  rewrite ?node_11716.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44245 (s : N.State) (i : N.Inputs) :
  R.v44245 (state s) (inputs i) = Zmod.unsigned (N.v44245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44245 s i)) at 1.
  unfold R.v44245, N.v44245.
  unfold R.v6, N.v6.
  rewrite ?node_11872.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44246 (s : N.State) (i : N.Inputs) :
  R.v44246 (state s) (inputs i) = Zmod.unsigned (N.v44246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44246 s i)) at 1.
  unfold R.v44246, N.v44246.
  rewrite ?node_44244.
  rewrite ?node_44245.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44247 (s : N.State) (i : N.Inputs) :
  R.v44247 (state s) (inputs i) = Zmod.unsigned (N.v44247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44247 s i)) at 1.
  unfold R.v44247, N.v44247.
  rewrite ?node_44243.
  rewrite ?node_44246.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44248 (s : N.State) (i : N.Inputs) :
  R.v44248 (state s) (inputs i) = Zmod.unsigned (N.v44248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44248 s i)) at 1.
  unfold R.v44248, N.v44248.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44249 (s : N.State) (i : N.Inputs) :
  R.v44249 (state s) (inputs i) = Zmod.unsigned (N.v44249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44249 s i)) at 1.
  unfold R.v44249, N.v44249.
  rewrite ?node_11727.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44250 (s : N.State) (i : N.Inputs) :
  R.v44250 (state s) (inputs i) = Zmod.unsigned (N.v44250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44250 s i)) at 1.
  unfold R.v44250, N.v44250.
  unfold R.v6, N.v6.
  rewrite ?node_11723.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44251 (s : N.State) (i : N.Inputs) :
  R.v44251 (state s) (inputs i) = Zmod.unsigned (N.v44251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44251 s i)) at 1.
  unfold R.v44251, N.v44251.
  unfold R.v6, N.v6.
  rewrite ?node_11716.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44252 (s : N.State) (i : N.Inputs) :
  R.v44252 (state s) (inputs i) = Zmod.unsigned (N.v44252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44252 s i)) at 1.
  unfold R.v44252, N.v44252.
  rewrite ?node_44250.
  rewrite ?node_44251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44253 (s : N.State) (i : N.Inputs) :
  R.v44253 (state s) (inputs i) = Zmod.unsigned (N.v44253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44253 s i)) at 1.
  unfold R.v44253, N.v44253.
  unfold R.v16484, N.v16484.
  rewrite ?node_44252.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44254 (s : N.State) (i : N.Inputs) :
  R.v44254 (state s) (inputs i) = Zmod.unsigned (N.v44254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44254 s i)) at 1.
  unfold R.v44254, N.v44254.
  rewrite ?node_44249.
  rewrite ?node_44253.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44255 (s : N.State) (i : N.Inputs) :
  R.v44255 (state s) (inputs i) = Zmod.unsigned (N.v44255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44255 s i)) at 1.
  unfold R.v44255, N.v44255.
  unfold R.v6, N.v6.
  rewrite ?node_44254.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44256 (s : N.State) (i : N.Inputs) :
  R.v44256 (state s) (inputs i) = Zmod.unsigned (N.v44256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44256 s i)) at 1.
  unfold R.v44256, N.v44256.
  rewrite ?node_11728.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44257 (s : N.State) (i : N.Inputs) :
  R.v44257 (state s) (inputs i) = Zmod.unsigned (N.v44257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44257 s i)) at 1.
  unfold R.v44257, N.v44257.
  unfold R.v6, N.v6.
  rewrite ?node_11947.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44258 (s : N.State) (i : N.Inputs) :
  R.v44258 (state s) (inputs i) = Zmod.unsigned (N.v44258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44258 s i)) at 1.
  unfold R.v44258, N.v44258.
  rewrite ?node_44256.
  rewrite ?node_44257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44259 (s : N.State) (i : N.Inputs) :
  R.v44259 (state s) (inputs i) = Zmod.unsigned (N.v44259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44259 s i)) at 1.
  unfold R.v44259, N.v44259.
  rewrite ?node_44255.
  rewrite ?node_44258.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44260 (s : N.State) (i : N.Inputs) :
  R.v44260 (state s) (inputs i) = Zmod.unsigned (N.v44260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44260 s i)) at 1.
  unfold R.v44260, N.v44260.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44261 (s : N.State) (i : N.Inputs) :
  R.v44261 (state s) (inputs i) = Zmod.unsigned (N.v44261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44261 s i)) at 1.
  unfold R.v44261, N.v44261.
  rewrite ?node_11756.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44262 (s : N.State) (i : N.Inputs) :
  R.v44262 (state s) (inputs i) = Zmod.unsigned (N.v44262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44262 s i)) at 1.
  unfold R.v44262, N.v44262.
  rewrite ?node_11752.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44263 (s : N.State) (i : N.Inputs) :
  R.v44263 (state s) (inputs i) = Zmod.unsigned (N.v44263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44263 s i)) at 1.
  unfold R.v44263, N.v44263.
  rewrite ?node_11750.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44264 (s : N.State) (i : N.Inputs) :
  R.v44264 (state s) (inputs i) = Zmod.unsigned (N.v44264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44264 s i)) at 1.
  unfold R.v44264, N.v44264.
  unfold R.v6, N.v6.
  rewrite ?node_11742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44265 (s : N.State) (i : N.Inputs) :
  R.v44265 (state s) (inputs i) = Zmod.unsigned (N.v44265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44265 s i)) at 1.
  unfold R.v44265, N.v44265.
  unfold R.v6, N.v6.
  rewrite ?node_11735.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44266 (s : N.State) (i : N.Inputs) :
  R.v44266 (state s) (inputs i) = Zmod.unsigned (N.v44266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44266 s i)) at 1.
  unfold R.v44266, N.v44266.
  rewrite ?node_44264.
  rewrite ?node_44265.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44267 (s : N.State) (i : N.Inputs) :
  R.v44267 (state s) (inputs i) = Zmod.unsigned (N.v44267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44267 s i)) at 1.
  unfold R.v44267, N.v44267.
  unfold R.v16484, N.v16484.
  rewrite ?node_44266.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44268 (s : N.State) (i : N.Inputs) :
  R.v44268 (state s) (inputs i) = Zmod.unsigned (N.v44268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44268 s i)) at 1.
  unfold R.v44268, N.v44268.
  rewrite ?node_44261.
  rewrite ?node_44262.
  rewrite ?node_44263.
  rewrite ?node_44267.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44269 (s : N.State) (i : N.Inputs) :
  R.v44269 (state s) (inputs i) = Zmod.unsigned (N.v44269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44269 s i)) at 1.
  unfold R.v44269, N.v44269.
  unfold R.v6, N.v6.
  rewrite ?node_44268.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44270 (s : N.State) (i : N.Inputs) :
  R.v44270 (state s) (inputs i) = Zmod.unsigned (N.v44270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44270 s i)) at 1.
  unfold R.v44270, N.v44270.
  rewrite ?node_11757.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44271 (s : N.State) (i : N.Inputs) :
  R.v44271 (state s) (inputs i) = Zmod.unsigned (N.v44271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44271 s i)) at 1.
  unfold R.v44271, N.v44271.
  unfold R.v6, N.v6.
  rewrite ?node_11900.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44272 (s : N.State) (i : N.Inputs) :
  R.v44272 (state s) (inputs i) = Zmod.unsigned (N.v44272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44272 s i)) at 1.
  unfold R.v44272, N.v44272.
  unfold R.v6, N.v6.
  rewrite ?node_11950.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44273 (s : N.State) (i : N.Inputs) :
  R.v44273 (state s) (inputs i) = Zmod.unsigned (N.v44273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44273 s i)) at 1.
  unfold R.v44273, N.v44273.
  rewrite ?node_44270.
  rewrite ?node_44271.
  rewrite ?node_44272.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44274 (s : N.State) (i : N.Inputs) :
  R.v44274 (state s) (inputs i) = Zmod.unsigned (N.v44274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44274 s i)) at 1.
  unfold R.v44274, N.v44274.
  rewrite ?node_44269.
  rewrite ?node_44273.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44275 (s : N.State) (i : N.Inputs) :
  R.v44275 (state s) (inputs i) = Zmod.unsigned (N.v44275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44275 s i)) at 1.
  unfold R.v44275, N.v44275.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44276 (s : N.State) (i : N.Inputs) :
  R.v44276 (state s) (inputs i) = Zmod.unsigned (N.v44276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44276 s i)) at 1.
  unfold R.v44276, N.v44276.
  rewrite ?node_11750.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44277 (s : N.State) (i : N.Inputs) :
  R.v44277 (state s) (inputs i) = Zmod.unsigned (N.v44277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44277 s i)) at 1.
  unfold R.v44277, N.v44277.
  unfold R.v6, N.v6.
  rewrite ?node_11742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44278 (s : N.State) (i : N.Inputs) :
  R.v44278 (state s) (inputs i) = Zmod.unsigned (N.v44278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44278 s i)) at 1.
  unfold R.v44278, N.v44278.
  unfold R.v6, N.v6.
  rewrite ?node_11735.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44279 (s : N.State) (i : N.Inputs) :
  R.v44279 (state s) (inputs i) = Zmod.unsigned (N.v44279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44279 s i)) at 1.
  unfold R.v44279, N.v44279.
  rewrite ?node_44277.
  rewrite ?node_44278.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44280 (s : N.State) (i : N.Inputs) :
  R.v44280 (state s) (inputs i) = Zmod.unsigned (N.v44280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44280 s i)) at 1.
  unfold R.v44280, N.v44280.
  unfold R.v16484, N.v16484.
  rewrite ?node_44279.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44281 (s : N.State) (i : N.Inputs) :
  R.v44281 (state s) (inputs i) = Zmod.unsigned (N.v44281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44281 s i)) at 1.
  unfold R.v44281, N.v44281.
  rewrite ?node_44276.
  rewrite ?node_44280.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44282 (s : N.State) (i : N.Inputs) :
  R.v44282 (state s) (inputs i) = Zmod.unsigned (N.v44282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44282 s i)) at 1.
  unfold R.v44282, N.v44282.
  unfold R.v6, N.v6.
  rewrite ?node_44281.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44283 (s : N.State) (i : N.Inputs) :
  R.v44283 (state s) (inputs i) = Zmod.unsigned (N.v44283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44283 s i)) at 1.
  unfold R.v44283, N.v44283.
  rewrite ?node_11751.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44284 (s : N.State) (i : N.Inputs) :
  R.v44284 (state s) (inputs i) = Zmod.unsigned (N.v44284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44284 s i)) at 1.
  unfold R.v44284, N.v44284.
  unfold R.v6, N.v6.
  rewrite ?node_11900.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44285 (s : N.State) (i : N.Inputs) :
  R.v44285 (state s) (inputs i) = Zmod.unsigned (N.v44285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44285 s i)) at 1.
  unfold R.v44285, N.v44285.
  rewrite ?node_44283.
  rewrite ?node_44284.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44286 (s : N.State) (i : N.Inputs) :
  R.v44286 (state s) (inputs i) = Zmod.unsigned (N.v44286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44286 s i)) at 1.
  unfold R.v44286, N.v44286.
  rewrite ?node_44282.
  rewrite ?node_44285.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44287 (s : N.State) (i : N.Inputs) :
  R.v44287 (state s) (inputs i) = Zmod.unsigned (N.v44287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44287 s i)) at 1.
  unfold R.v44287, N.v44287.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44288 (s : N.State) (i : N.Inputs) :
  R.v44288 (state s) (inputs i) = Zmod.unsigned (N.v44288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44288 s i)) at 1.
  unfold R.v44288, N.v44288.
  rewrite ?node_11756.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44289 (s : N.State) (i : N.Inputs) :
  R.v44289 (state s) (inputs i) = Zmod.unsigned (N.v44289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44289 s i)) at 1.
  unfold R.v44289, N.v44289.
  unfold R.v6, N.v6.
  rewrite ?node_11752.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44290 (s : N.State) (i : N.Inputs) :
  R.v44290 (state s) (inputs i) = Zmod.unsigned (N.v44290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44290 s i)) at 1.
  unfold R.v44290, N.v44290.
  unfold R.v6, N.v6.
  rewrite ?node_11751.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44291 (s : N.State) (i : N.Inputs) :
  R.v44291 (state s) (inputs i) = Zmod.unsigned (N.v44291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44291 s i)) at 1.
  unfold R.v44291, N.v44291.
  rewrite ?node_44289.
  rewrite ?node_44290.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44292 (s : N.State) (i : N.Inputs) :
  R.v44292 (state s) (inputs i) = Zmod.unsigned (N.v44292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44292 s i)) at 1.
  unfold R.v44292, N.v44292.
  unfold R.v16484, N.v16484.
  rewrite ?node_44291.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44293 (s : N.State) (i : N.Inputs) :
  R.v44293 (state s) (inputs i) = Zmod.unsigned (N.v44293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44293 s i)) at 1.
  unfold R.v44293, N.v44293.
  rewrite ?node_44288.
  rewrite ?node_44292.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44294 (s : N.State) (i : N.Inputs) :
  R.v44294 (state s) (inputs i) = Zmod.unsigned (N.v44294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44294 s i)) at 1.
  unfold R.v44294, N.v44294.
  unfold R.v6, N.v6.
  rewrite ?node_44293.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44295 (s : N.State) (i : N.Inputs) :
  R.v44295 (state s) (inputs i) = Zmod.unsigned (N.v44295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44295 s i)) at 1.
  unfold R.v44295, N.v44295.
  rewrite ?node_11757.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44296 (s : N.State) (i : N.Inputs) :
  R.v44296 (state s) (inputs i) = Zmod.unsigned (N.v44296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44296 s i)) at 1.
  unfold R.v44296, N.v44296.
  unfold R.v6, N.v6.
  rewrite ?node_11950.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44297 (s : N.State) (i : N.Inputs) :
  R.v44297 (state s) (inputs i) = Zmod.unsigned (N.v44297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44297 s i)) at 1.
  unfold R.v44297, N.v44297.
  rewrite ?node_44295.
  rewrite ?node_44296.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44298 (s : N.State) (i : N.Inputs) :
  R.v44298 (state s) (inputs i) = Zmod.unsigned (N.v44298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44298 s i)) at 1.
  unfold R.v44298, N.v44298.
  rewrite ?node_44294.
  rewrite ?node_44297.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44299 (s : N.State) (i : N.Inputs) :
  R.v44299 (state s) (inputs i) = Zmod.unsigned (N.v44299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44299 s i)) at 1.
  unfold R.v44299, N.v44299.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44300 (s : N.State) (i : N.Inputs) :
  R.v44300 (state s) (inputs i) = Zmod.unsigned (N.v44300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44300 s i)) at 1.
  unfold R.v44300, N.v44300.
  rewrite ?node_11776.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44301 (s : N.State) (i : N.Inputs) :
  R.v44301 (state s) (inputs i) = Zmod.unsigned (N.v44301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44301 s i)) at 1.
  unfold R.v44301, N.v44301.
  rewrite ?node_11772.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44302 (s : N.State) (i : N.Inputs) :
  R.v44302 (state s) (inputs i) = Zmod.unsigned (N.v44302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44302 s i)) at 1.
  unfold R.v44302, N.v44302.
  rewrite ?node_11768.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44303 (s : N.State) (i : N.Inputs) :
  R.v44303 (state s) (inputs i) = Zmod.unsigned (N.v44303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44303 s i)) at 1.
  unfold R.v44303, N.v44303.
  unfold R.v6, N.v6.
  rewrite ?node_11764.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44304 (s : N.State) (i : N.Inputs) :
  R.v44304 (state s) (inputs i) = Zmod.unsigned (N.v44304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44304 s i)) at 1.
  unfold R.v44304, N.v44304.
  unfold R.v6, N.v6.
  rewrite ?node_11761.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44305 (s : N.State) (i : N.Inputs) :
  R.v44305 (state s) (inputs i) = Zmod.unsigned (N.v44305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44305 s i)) at 1.
  unfold R.v44305, N.v44305.
  rewrite ?node_44303.
  rewrite ?node_44304.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44306 (s : N.State) (i : N.Inputs) :
  R.v44306 (state s) (inputs i) = Zmod.unsigned (N.v44306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44306 s i)) at 1.
  unfold R.v44306, N.v44306.
  unfold R.v16484, N.v16484.
  rewrite ?node_44305.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44307 (s : N.State) (i : N.Inputs) :
  R.v44307 (state s) (inputs i) = Zmod.unsigned (N.v44307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44307 s i)) at 1.
  unfold R.v44307, N.v44307.
  rewrite ?node_44300.
  rewrite ?node_44301.
  rewrite ?node_44302.
  rewrite ?node_44306.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44308 (s : N.State) (i : N.Inputs) :
  R.v44308 (state s) (inputs i) = Zmod.unsigned (N.v44308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44308 s i)) at 1.
  unfold R.v44308, N.v44308.
  unfold R.v6, N.v6.
  rewrite ?node_44307.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44309 (s : N.State) (i : N.Inputs) :
  R.v44309 (state s) (inputs i) = Zmod.unsigned (N.v44309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44309 s i)) at 1.
  unfold R.v44309, N.v44309.
  rewrite ?node_11777.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44310 (s : N.State) (i : N.Inputs) :
  R.v44310 (state s) (inputs i) = Zmod.unsigned (N.v44310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44310 s i)) at 1.
  unfold R.v44310, N.v44310.
  unfold R.v6, N.v6.
  rewrite ?node_11920.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44311 (s : N.State) (i : N.Inputs) :
  R.v44311 (state s) (inputs i) = Zmod.unsigned (N.v44311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44311 s i)) at 1.
  unfold R.v44311, N.v44311.
  unfold R.v6, N.v6.
  rewrite ?node_11954.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44312 (s : N.State) (i : N.Inputs) :
  R.v44312 (state s) (inputs i) = Zmod.unsigned (N.v44312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44312 s i)) at 1.
  unfold R.v44312, N.v44312.
  rewrite ?node_44309.
  rewrite ?node_44310.
  rewrite ?node_44311.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44313 (s : N.State) (i : N.Inputs) :
  R.v44313 (state s) (inputs i) = Zmod.unsigned (N.v44313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44313 s i)) at 1.
  unfold R.v44313, N.v44313.
  rewrite ?node_44308.
  rewrite ?node_44312.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44314 (s : N.State) (i : N.Inputs) :
  R.v44314 (state s) (inputs i) = Zmod.unsigned (N.v44314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44314 s i)) at 1.
  unfold R.v44314, N.v44314.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44315 (s : N.State) (i : N.Inputs) :
  R.v44315 (state s) (inputs i) = Zmod.unsigned (N.v44315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44315 s i)) at 1.
  unfold R.v44315, N.v44315.
  rewrite ?node_11768.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44316 (s : N.State) (i : N.Inputs) :
  R.v44316 (state s) (inputs i) = Zmod.unsigned (N.v44316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44316 s i)) at 1.
  unfold R.v44316, N.v44316.
  unfold R.v6, N.v6.
  rewrite ?node_11764.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44317 (s : N.State) (i : N.Inputs) :
  R.v44317 (state s) (inputs i) = Zmod.unsigned (N.v44317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44317 s i)) at 1.
  unfold R.v44317, N.v44317.
  unfold R.v6, N.v6.
  rewrite ?node_11761.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44318 (s : N.State) (i : N.Inputs) :
  R.v44318 (state s) (inputs i) = Zmod.unsigned (N.v44318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44318 s i)) at 1.
  unfold R.v44318, N.v44318.
  rewrite ?node_44316.
  rewrite ?node_44317.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44319 (s : N.State) (i : N.Inputs) :
  R.v44319 (state s) (inputs i) = Zmod.unsigned (N.v44319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44319 s i)) at 1.
  unfold R.v44319, N.v44319.
  unfold R.v16484, N.v16484.
  rewrite ?node_44318.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44320 (s : N.State) (i : N.Inputs) :
  R.v44320 (state s) (inputs i) = Zmod.unsigned (N.v44320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44320 s i)) at 1.
  unfold R.v44320, N.v44320.
  rewrite ?node_44315.
  rewrite ?node_44319.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44321 (s : N.State) (i : N.Inputs) :
  R.v44321 (state s) (inputs i) = Zmod.unsigned (N.v44321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44321 s i)) at 1.
  unfold R.v44321, N.v44321.
  unfold R.v6, N.v6.
  rewrite ?node_44320.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44322 (s : N.State) (i : N.Inputs) :
  R.v44322 (state s) (inputs i) = Zmod.unsigned (N.v44322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44322 s i)) at 1.
  unfold R.v44322, N.v44322.
  rewrite ?node_11769.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44323 (s : N.State) (i : N.Inputs) :
  R.v44323 (state s) (inputs i) = Zmod.unsigned (N.v44323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44323 s i)) at 1.
  unfold R.v44323, N.v44323.
  unfold R.v6, N.v6.
  rewrite ?node_11920.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44324 (s : N.State) (i : N.Inputs) :
  R.v44324 (state s) (inputs i) = Zmod.unsigned (N.v44324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44324 s i)) at 1.
  unfold R.v44324, N.v44324.
  rewrite ?node_44322.
  rewrite ?node_44323.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44325 (s : N.State) (i : N.Inputs) :
  R.v44325 (state s) (inputs i) = Zmod.unsigned (N.v44325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44325 s i)) at 1.
  unfold R.v44325, N.v44325.
  rewrite ?node_44321.
  rewrite ?node_44324.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44326 (s : N.State) (i : N.Inputs) :
  R.v44326 (state s) (inputs i) = Zmod.unsigned (N.v44326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44326 s i)) at 1.
  unfold R.v44326, N.v44326.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44327 (s : N.State) (i : N.Inputs) :
  R.v44327 (state s) (inputs i) = Zmod.unsigned (N.v44327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44327 s i)) at 1.
  unfold R.v44327, N.v44327.
  rewrite ?node_11776.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44328 (s : N.State) (i : N.Inputs) :
  R.v44328 (state s) (inputs i) = Zmod.unsigned (N.v44328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44328 s i)) at 1.
  unfold R.v44328, N.v44328.
  unfold R.v6, N.v6.
  rewrite ?node_11772.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44329 (s : N.State) (i : N.Inputs) :
  R.v44329 (state s) (inputs i) = Zmod.unsigned (N.v44329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44329 s i)) at 1.
  unfold R.v44329, N.v44329.
  unfold R.v6, N.v6.
  rewrite ?node_11769.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44330 (s : N.State) (i : N.Inputs) :
  R.v44330 (state s) (inputs i) = Zmod.unsigned (N.v44330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44330 s i)) at 1.
  unfold R.v44330, N.v44330.
  rewrite ?node_44328.
  rewrite ?node_44329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44331 (s : N.State) (i : N.Inputs) :
  R.v44331 (state s) (inputs i) = Zmod.unsigned (N.v44331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44331 s i)) at 1.
  unfold R.v44331, N.v44331.
  unfold R.v16484, N.v16484.
  rewrite ?node_44330.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44332 (s : N.State) (i : N.Inputs) :
  R.v44332 (state s) (inputs i) = Zmod.unsigned (N.v44332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44332 s i)) at 1.
  unfold R.v44332, N.v44332.
  rewrite ?node_44327.
  rewrite ?node_44331.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44333 (s : N.State) (i : N.Inputs) :
  R.v44333 (state s) (inputs i) = Zmod.unsigned (N.v44333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44333 s i)) at 1.
  unfold R.v44333, N.v44333.
  unfold R.v6, N.v6.
  rewrite ?node_44332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44334 (s : N.State) (i : N.Inputs) :
  R.v44334 (state s) (inputs i) = Zmod.unsigned (N.v44334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44334 s i)) at 1.
  unfold R.v44334, N.v44334.
  rewrite ?node_11777.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44335 (s : N.State) (i : N.Inputs) :
  R.v44335 (state s) (inputs i) = Zmod.unsigned (N.v44335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44335 s i)) at 1.
  unfold R.v44335, N.v44335.
  unfold R.v6, N.v6.
  rewrite ?node_11954.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44336 (s : N.State) (i : N.Inputs) :
  R.v44336 (state s) (inputs i) = Zmod.unsigned (N.v44336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44336 s i)) at 1.
  unfold R.v44336, N.v44336.
  rewrite ?node_44334.
  rewrite ?node_44335.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44337 (s : N.State) (i : N.Inputs) :
  R.v44337 (state s) (inputs i) = Zmod.unsigned (N.v44337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44337 s i)) at 1.
  unfold R.v44337, N.v44337.
  rewrite ?node_44333.
  rewrite ?node_44336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44338 (s : N.State) (i : N.Inputs) :
  R.v44338 (state s) (inputs i) = Zmod.unsigned (N.v44338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44338 s i)) at 1.
  unfold R.v44338, N.v44338.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44339 (s : N.State) (i : N.Inputs) :
  R.v44339 (state s) (inputs i) = Zmod.unsigned (N.v44339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44339 s i)) at 1.
  unfold R.v44339, N.v44339.
  rewrite ?node_11794.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44340 (s : N.State) (i : N.Inputs) :
  R.v44340 (state s) (inputs i) = Zmod.unsigned (N.v44340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44340 s i)) at 1.
  unfold R.v44340, N.v44340.
  rewrite ?node_11790.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44341 (s : N.State) (i : N.Inputs) :
  R.v44341 (state s) (inputs i) = Zmod.unsigned (N.v44341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44341 s i)) at 1.
  unfold R.v44341, N.v44341.
  rewrite ?node_11788.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44342 (s : N.State) (i : N.Inputs) :
  R.v44342 (state s) (inputs i) = Zmod.unsigned (N.v44342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44342 s i)) at 1.
  unfold R.v44342, N.v44342.
  unfold R.v6, N.v6.
  rewrite ?node_11784.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44343 (s : N.State) (i : N.Inputs) :
  R.v44343 (state s) (inputs i) = Zmod.unsigned (N.v44343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44343 s i)) at 1.
  unfold R.v44343, N.v44343.
  unfold R.v6, N.v6.
  rewrite ?node_11781.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44344 (s : N.State) (i : N.Inputs) :
  R.v44344 (state s) (inputs i) = Zmod.unsigned (N.v44344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44344 s i)) at 1.
  unfold R.v44344, N.v44344.
  rewrite ?node_44342.
  rewrite ?node_44343.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44345 (s : N.State) (i : N.Inputs) :
  R.v44345 (state s) (inputs i) = Zmod.unsigned (N.v44345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44345 s i)) at 1.
  unfold R.v44345, N.v44345.
  unfold R.v16484, N.v16484.
  rewrite ?node_44344.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44346 (s : N.State) (i : N.Inputs) :
  R.v44346 (state s) (inputs i) = Zmod.unsigned (N.v44346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44346 s i)) at 1.
  unfold R.v44346, N.v44346.
  rewrite ?node_44339.
  rewrite ?node_44340.
  rewrite ?node_44341.
  rewrite ?node_44345.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44347 (s : N.State) (i : N.Inputs) :
  R.v44347 (state s) (inputs i) = Zmod.unsigned (N.v44347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44347 s i)) at 1.
  unfold R.v44347, N.v44347.
  unfold R.v6, N.v6.
  rewrite ?node_44346.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44348 (s : N.State) (i : N.Inputs) :
  R.v44348 (state s) (inputs i) = Zmod.unsigned (N.v44348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44348 s i)) at 1.
  unfold R.v44348, N.v44348.
  rewrite ?node_11795.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44349 (s : N.State) (i : N.Inputs) :
  R.v44349 (state s) (inputs i) = Zmod.unsigned (N.v44349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44349 s i)) at 1.
  unfold R.v44349, N.v44349.
  unfold R.v6, N.v6.
  rewrite ?node_11938.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44350 (s : N.State) (i : N.Inputs) :
  R.v44350 (state s) (inputs i) = Zmod.unsigned (N.v44350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44350 s i)) at 1.
  unfold R.v44350, N.v44350.
  unfold R.v6, N.v6.
  rewrite ?node_11958.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44351 (s : N.State) (i : N.Inputs) :
  R.v44351 (state s) (inputs i) = Zmod.unsigned (N.v44351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44351 s i)) at 1.
  unfold R.v44351, N.v44351.
  rewrite ?node_44348.
  rewrite ?node_44349.
  rewrite ?node_44350.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44352 (s : N.State) (i : N.Inputs) :
  R.v44352 (state s) (inputs i) = Zmod.unsigned (N.v44352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44352 s i)) at 1.
  unfold R.v44352, N.v44352.
  rewrite ?node_44347.
  rewrite ?node_44351.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44353 (s : N.State) (i : N.Inputs) :
  R.v44353 (state s) (inputs i) = Zmod.unsigned (N.v44353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44353 s i)) at 1.
  unfold R.v44353, N.v44353.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44354 (s : N.State) (i : N.Inputs) :
  R.v44354 (state s) (inputs i) = Zmod.unsigned (N.v44354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44354 s i)) at 1.
  unfold R.v44354, N.v44354.
  rewrite ?node_11788.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44355 (s : N.State) (i : N.Inputs) :
  R.v44355 (state s) (inputs i) = Zmod.unsigned (N.v44355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44355 s i)) at 1.
  unfold R.v44355, N.v44355.
  unfold R.v6, N.v6.
  rewrite ?node_11784.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44356 (s : N.State) (i : N.Inputs) :
  R.v44356 (state s) (inputs i) = Zmod.unsigned (N.v44356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44356 s i)) at 1.
  unfold R.v44356, N.v44356.
  unfold R.v6, N.v6.
  rewrite ?node_11781.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44357 (s : N.State) (i : N.Inputs) :
  R.v44357 (state s) (inputs i) = Zmod.unsigned (N.v44357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44357 s i)) at 1.
  unfold R.v44357, N.v44357.
  rewrite ?node_44355.
  rewrite ?node_44356.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44358 (s : N.State) (i : N.Inputs) :
  R.v44358 (state s) (inputs i) = Zmod.unsigned (N.v44358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44358 s i)) at 1.
  unfold R.v44358, N.v44358.
  unfold R.v16484, N.v16484.
  rewrite ?node_44357.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44359 (s : N.State) (i : N.Inputs) :
  R.v44359 (state s) (inputs i) = Zmod.unsigned (N.v44359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44359 s i)) at 1.
  unfold R.v44359, N.v44359.
  rewrite ?node_44354.
  rewrite ?node_44358.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44360 (s : N.State) (i : N.Inputs) :
  R.v44360 (state s) (inputs i) = Zmod.unsigned (N.v44360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44360 s i)) at 1.
  unfold R.v44360, N.v44360.
  unfold R.v6, N.v6.
  rewrite ?node_44359.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44361 (s : N.State) (i : N.Inputs) :
  R.v44361 (state s) (inputs i) = Zmod.unsigned (N.v44361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44361 s i)) at 1.
  unfold R.v44361, N.v44361.
  rewrite ?node_11789.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44362 (s : N.State) (i : N.Inputs) :
  R.v44362 (state s) (inputs i) = Zmod.unsigned (N.v44362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44362 s i)) at 1.
  unfold R.v44362, N.v44362.
  unfold R.v6, N.v6.
  rewrite ?node_11938.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44363 (s : N.State) (i : N.Inputs) :
  R.v44363 (state s) (inputs i) = Zmod.unsigned (N.v44363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44363 s i)) at 1.
  unfold R.v44363, N.v44363.
  rewrite ?node_44361.
  rewrite ?node_44362.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44364 (s : N.State) (i : N.Inputs) :
  R.v44364 (state s) (inputs i) = Zmod.unsigned (N.v44364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44364 s i)) at 1.
  unfold R.v44364, N.v44364.
  rewrite ?node_44360.
  rewrite ?node_44363.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44365 (s : N.State) (i : N.Inputs) :
  R.v44365 (state s) (inputs i) = Zmod.unsigned (N.v44365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44365 s i)) at 1.
  unfold R.v44365, N.v44365.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44366 (s : N.State) (i : N.Inputs) :
  R.v44366 (state s) (inputs i) = Zmod.unsigned (N.v44366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44366 s i)) at 1.
  unfold R.v44366, N.v44366.
  rewrite ?node_11794.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44367 (s : N.State) (i : N.Inputs) :
  R.v44367 (state s) (inputs i) = Zmod.unsigned (N.v44367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44367 s i)) at 1.
  unfold R.v44367, N.v44367.
  unfold R.v6, N.v6.
  rewrite ?node_11790.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44368 (s : N.State) (i : N.Inputs) :
  R.v44368 (state s) (inputs i) = Zmod.unsigned (N.v44368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44368 s i)) at 1.
  unfold R.v44368, N.v44368.
  unfold R.v6, N.v6.
  rewrite ?node_11789.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44369 (s : N.State) (i : N.Inputs) :
  R.v44369 (state s) (inputs i) = Zmod.unsigned (N.v44369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44369 s i)) at 1.
  unfold R.v44369, N.v44369.
  rewrite ?node_44367.
  rewrite ?node_44368.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44370 (s : N.State) (i : N.Inputs) :
  R.v44370 (state s) (inputs i) = Zmod.unsigned (N.v44370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44370 s i)) at 1.
  unfold R.v44370, N.v44370.
  unfold R.v16484, N.v16484.
  rewrite ?node_44369.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44371 (s : N.State) (i : N.Inputs) :
  R.v44371 (state s) (inputs i) = Zmod.unsigned (N.v44371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44371 s i)) at 1.
  unfold R.v44371, N.v44371.
  rewrite ?node_44366.
  rewrite ?node_44370.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44372 (s : N.State) (i : N.Inputs) :
  R.v44372 (state s) (inputs i) = Zmod.unsigned (N.v44372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44372 s i)) at 1.
  unfold R.v44372, N.v44372.
  unfold R.v6, N.v6.
  rewrite ?node_44371.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44373 (s : N.State) (i : N.Inputs) :
  R.v44373 (state s) (inputs i) = Zmod.unsigned (N.v44373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44373 s i)) at 1.
  unfold R.v44373, N.v44373.
  rewrite ?node_11795.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44374 (s : N.State) (i : N.Inputs) :
  R.v44374 (state s) (inputs i) = Zmod.unsigned (N.v44374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44374 s i)) at 1.
  unfold R.v44374, N.v44374.
  unfold R.v6, N.v6.
  rewrite ?node_11958.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44375 (s : N.State) (i : N.Inputs) :
  R.v44375 (state s) (inputs i) = Zmod.unsigned (N.v44375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44375 s i)) at 1.
  unfold R.v44375, N.v44375.
  rewrite ?node_44373.
  rewrite ?node_44374.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44376 (s : N.State) (i : N.Inputs) :
  R.v44376 (state s) (inputs i) = Zmod.unsigned (N.v44376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44376 s i)) at 1.
  unfold R.v44376, N.v44376.
  rewrite ?node_44372.
  rewrite ?node_44375.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44377 (s : N.State) (i : N.Inputs) :
  R.v44377 (state s) (inputs i) = Zmod.unsigned (N.v44377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44377 s i)) at 1.
  unfold R.v44377, N.v44377.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44378 (s : N.State) (i : N.Inputs) :
  R.v44378 (state s) (inputs i) = Zmod.unsigned (N.v44378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44378 s i)) at 1.
  unfold R.v44378, N.v44378.
  rewrite ?node_11872.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44379 (s : N.State) (i : N.Inputs) :
  R.v44379 (state s) (inputs i) = Zmod.unsigned (N.v44379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44379 s i)) at 1.
  unfold R.v44379, N.v44379.
  rewrite ?node_11868.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44380 (s : N.State) (i : N.Inputs) :
  R.v44380 (state s) (inputs i) = Zmod.unsigned (N.v44380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44380 s i)) at 1.
  unfold R.v44380, N.v44380.
  rewrite ?node_11860.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44381 (s : N.State) (i : N.Inputs) :
  R.v44381 (state s) (inputs i) = Zmod.unsigned (N.v44381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44381 s i)) at 1.
  unfold R.v44381, N.v44381.
  unfold R.v6, N.v6.
  rewrite ?node_11852.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44382 (s : N.State) (i : N.Inputs) :
  R.v44382 (state s) (inputs i) = Zmod.unsigned (N.v44382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44382 s i)) at 1.
  unfold R.v44382, N.v44382.
  unfold R.v6, N.v6.
  rewrite ?node_11845.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44383 (s : N.State) (i : N.Inputs) :
  R.v44383 (state s) (inputs i) = Zmod.unsigned (N.v44383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44383 s i)) at 1.
  unfold R.v44383, N.v44383.
  rewrite ?node_44381.
  rewrite ?node_44382.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44384 (s : N.State) (i : N.Inputs) :
  R.v44384 (state s) (inputs i) = Zmod.unsigned (N.v44384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44384 s i)) at 1.
  unfold R.v44384, N.v44384.
  unfold R.v16484, N.v16484.
  rewrite ?node_44383.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44385 (s : N.State) (i : N.Inputs) :
  R.v44385 (state s) (inputs i) = Zmod.unsigned (N.v44385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44385 s i)) at 1.
  unfold R.v44385, N.v44385.
  rewrite ?node_44378.
  rewrite ?node_44379.
  rewrite ?node_44380.
  rewrite ?node_44384.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44386 (s : N.State) (i : N.Inputs) :
  R.v44386 (state s) (inputs i) = Zmod.unsigned (N.v44386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44386 s i)) at 1.
  unfold R.v44386, N.v44386.
  unfold R.v6, N.v6.
  rewrite ?node_44385.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44387 (s : N.State) (i : N.Inputs) :
  R.v44387 (state s) (inputs i) = Zmod.unsigned (N.v44387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44387 s i)) at 1.
  unfold R.v44387, N.v44387.
  rewrite ?node_11873.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44388 (s : N.State) (i : N.Inputs) :
  R.v44388 (state s) (inputs i) = Zmod.unsigned (N.v44388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44388 s i)) at 1.
  unfold R.v44388, N.v44388.
  unfold R.v6, N.v6.
  rewrite ?node_12017.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44389 (s : N.State) (i : N.Inputs) :
  R.v44389 (state s) (inputs i) = Zmod.unsigned (N.v44389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44389 s i)) at 1.
  unfold R.v44389, N.v44389.
  unfold R.v6, N.v6.
  rewrite ?node_12089.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44390 (s : N.State) (i : N.Inputs) :
  R.v44390 (state s) (inputs i) = Zmod.unsigned (N.v44390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44390 s i)) at 1.
  unfold R.v44390, N.v44390.
  rewrite ?node_44387.
  rewrite ?node_44388.
  rewrite ?node_44389.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44391 (s : N.State) (i : N.Inputs) :
  R.v44391 (state s) (inputs i) = Zmod.unsigned (N.v44391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44391 s i)) at 1.
  unfold R.v44391, N.v44391.
  rewrite ?node_44386.
  rewrite ?node_44390.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44392 (s : N.State) (i : N.Inputs) :
  R.v44392 (state s) (inputs i) = Zmod.unsigned (N.v44392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44392 s i)) at 1.
  unfold R.v44392, N.v44392.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44393 (s : N.State) (i : N.Inputs) :
  R.v44393 (state s) (inputs i) = Zmod.unsigned (N.v44393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44393 s i)) at 1.
  unfold R.v44393, N.v44393.
  rewrite ?node_11860.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44394 (s : N.State) (i : N.Inputs) :
  R.v44394 (state s) (inputs i) = Zmod.unsigned (N.v44394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44394 s i)) at 1.
  unfold R.v44394, N.v44394.
  unfold R.v6, N.v6.
  rewrite ?node_11852.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44395 (s : N.State) (i : N.Inputs) :
  R.v44395 (state s) (inputs i) = Zmod.unsigned (N.v44395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44395 s i)) at 1.
  unfold R.v44395, N.v44395.
  unfold R.v6, N.v6.
  rewrite ?node_11845.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44396 (s : N.State) (i : N.Inputs) :
  R.v44396 (state s) (inputs i) = Zmod.unsigned (N.v44396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44396 s i)) at 1.
  unfold R.v44396, N.v44396.
  rewrite ?node_44394.
  rewrite ?node_44395.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44397 (s : N.State) (i : N.Inputs) :
  R.v44397 (state s) (inputs i) = Zmod.unsigned (N.v44397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44397 s i)) at 1.
  unfold R.v44397, N.v44397.
  unfold R.v16484, N.v16484.
  rewrite ?node_44396.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44398 (s : N.State) (i : N.Inputs) :
  R.v44398 (state s) (inputs i) = Zmod.unsigned (N.v44398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44398 s i)) at 1.
  unfold R.v44398, N.v44398.
  rewrite ?node_44393.
  rewrite ?node_44397.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44399 (s : N.State) (i : N.Inputs) :
  R.v44399 (state s) (inputs i) = Zmod.unsigned (N.v44399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44399 s i)) at 1.
  unfold R.v44399, N.v44399.
  unfold R.v6, N.v6.
  rewrite ?node_44398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44400 (s : N.State) (i : N.Inputs) :
  R.v44400 (state s) (inputs i) = Zmod.unsigned (N.v44400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44400 s i)) at 1.
  unfold R.v44400, N.v44400.
  rewrite ?node_11861.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44401 (s : N.State) (i : N.Inputs) :
  R.v44401 (state s) (inputs i) = Zmod.unsigned (N.v44401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44401 s i)) at 1.
  unfold R.v44401, N.v44401.
  unfold R.v6, N.v6.
  rewrite ?node_12017.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44402 (s : N.State) (i : N.Inputs) :
  R.v44402 (state s) (inputs i) = Zmod.unsigned (N.v44402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44402 s i)) at 1.
  unfold R.v44402, N.v44402.
  rewrite ?node_44400.
  rewrite ?node_44401.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44403 (s : N.State) (i : N.Inputs) :
  R.v44403 (state s) (inputs i) = Zmod.unsigned (N.v44403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44403 s i)) at 1.
  unfold R.v44403, N.v44403.
  rewrite ?node_44399.
  rewrite ?node_44402.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44404 (s : N.State) (i : N.Inputs) :
  R.v44404 (state s) (inputs i) = Zmod.unsigned (N.v44404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44404 s i)) at 1.
  unfold R.v44404, N.v44404.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44405 (s : N.State) (i : N.Inputs) :
  R.v44405 (state s) (inputs i) = Zmod.unsigned (N.v44405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44405 s i)) at 1.
  unfold R.v44405, N.v44405.
  rewrite ?node_11872.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44406 (s : N.State) (i : N.Inputs) :
  R.v44406 (state s) (inputs i) = Zmod.unsigned (N.v44406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44406 s i)) at 1.
  unfold R.v44406, N.v44406.
  unfold R.v6, N.v6.
  rewrite ?node_11868.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44407 (s : N.State) (i : N.Inputs) :
  R.v44407 (state s) (inputs i) = Zmod.unsigned (N.v44407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44407 s i)) at 1.
  unfold R.v44407, N.v44407.
  unfold R.v6, N.v6.
  rewrite ?node_11861.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44408 (s : N.State) (i : N.Inputs) :
  R.v44408 (state s) (inputs i) = Zmod.unsigned (N.v44408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44408 s i)) at 1.
  unfold R.v44408, N.v44408.
  rewrite ?node_44406.
  rewrite ?node_44407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44409 (s : N.State) (i : N.Inputs) :
  R.v44409 (state s) (inputs i) = Zmod.unsigned (N.v44409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44409 s i)) at 1.
  unfold R.v44409, N.v44409.
  unfold R.v16484, N.v16484.
  rewrite ?node_44408.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44410 (s : N.State) (i : N.Inputs) :
  R.v44410 (state s) (inputs i) = Zmod.unsigned (N.v44410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44410 s i)) at 1.
  unfold R.v44410, N.v44410.
  rewrite ?node_44405.
  rewrite ?node_44409.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44411 (s : N.State) (i : N.Inputs) :
  R.v44411 (state s) (inputs i) = Zmod.unsigned (N.v44411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44411 s i)) at 1.
  unfold R.v44411, N.v44411.
  unfold R.v6, N.v6.
  rewrite ?node_44410.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44412 (s : N.State) (i : N.Inputs) :
  R.v44412 (state s) (inputs i) = Zmod.unsigned (N.v44412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44412 s i)) at 1.
  unfold R.v44412, N.v44412.
  rewrite ?node_11873.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44413 (s : N.State) (i : N.Inputs) :
  R.v44413 (state s) (inputs i) = Zmod.unsigned (N.v44413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44413 s i)) at 1.
  unfold R.v44413, N.v44413.
  unfold R.v6, N.v6.
  rewrite ?node_12089.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44414 (s : N.State) (i : N.Inputs) :
  R.v44414 (state s) (inputs i) = Zmod.unsigned (N.v44414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44414 s i)) at 1.
  unfold R.v44414, N.v44414.
  rewrite ?node_44412.
  rewrite ?node_44413.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44415 (s : N.State) (i : N.Inputs) :
  R.v44415 (state s) (inputs i) = Zmod.unsigned (N.v44415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44415 s i)) at 1.
  unfold R.v44415, N.v44415.
  rewrite ?node_44411.
  rewrite ?node_44414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44416 (s : N.State) (i : N.Inputs) :
  R.v44416 (state s) (inputs i) = Zmod.unsigned (N.v44416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44416 s i)) at 1.
  unfold R.v44416, N.v44416.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44417 (s : N.State) (i : N.Inputs) :
  R.v44417 (state s) (inputs i) = Zmod.unsigned (N.v44417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44417 s i)) at 1.
  unfold R.v44417, N.v44417.
  rewrite ?node_11900.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44418 (s : N.State) (i : N.Inputs) :
  R.v44418 (state s) (inputs i) = Zmod.unsigned (N.v44418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44418 s i)) at 1.
  unfold R.v44418, N.v44418.
  unfold R.v16463, N.v16463.
  rewrite !state_r1466_nr_5F1469.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1466_nr_5F1469 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44419 (s : N.State) (i : N.Inputs) :
  R.v44419 (state s) (inputs i) = Zmod.unsigned (N.v44419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44419 s i)) at 1.
  unfold R.v44419, N.v44419.
  rewrite ?node_11895.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44420 (s : N.State) (i : N.Inputs) :
  R.v44420 (state s) (inputs i) = Zmod.unsigned (N.v44420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44420 s i)) at 1.
  unfold R.v44420, N.v44420.
  unfold R.v6, N.v6.
  rewrite ?node_11887.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44421 (s : N.State) (i : N.Inputs) :
  R.v44421 (state s) (inputs i) = Zmod.unsigned (N.v44421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44421 s i)) at 1.
  unfold R.v44421, N.v44421.
  unfold R.v6, N.v6.
  rewrite ?node_11880.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44422 (s : N.State) (i : N.Inputs) :
  R.v44422 (state s) (inputs i) = Zmod.unsigned (N.v44422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44422 s i)) at 1.
  unfold R.v44422, N.v44422.
  rewrite ?node_44420.
  rewrite ?node_44421.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44423 (s : N.State) (i : N.Inputs) :
  R.v44423 (state s) (inputs i) = Zmod.unsigned (N.v44423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44423 s i)) at 1.
  unfold R.v44423, N.v44423.
  unfold R.v16484, N.v16484.
  rewrite ?node_44422.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44424 (s : N.State) (i : N.Inputs) :
  R.v44424 (state s) (inputs i) = Zmod.unsigned (N.v44424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44424 s i)) at 1.
  unfold R.v44424, N.v44424.
  rewrite ?node_44417.
  rewrite ?node_44418.
  rewrite ?node_44419.
  rewrite ?node_44423.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44425 (s : N.State) (i : N.Inputs) :
  R.v44425 (state s) (inputs i) = Zmod.unsigned (N.v44425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44425 s i)) at 1.
  unfold R.v44425, N.v44425.
  unfold R.v6, N.v6.
  rewrite ?node_44424.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44426 (s : N.State) (i : N.Inputs) :
  R.v44426 (state s) (inputs i) = Zmod.unsigned (N.v44426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44426 s i)) at 1.
  unfold R.v44426, N.v44426.
  rewrite ?node_11901.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44427 (s : N.State) (i : N.Inputs) :
  R.v44427 (state s) (inputs i) = Zmod.unsigned (N.v44427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44427 s i)) at 1.
  unfold R.v44427, N.v44427.
  unfold R.v6, N.v6.
  rewrite ?node_12045.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44428 (s : N.State) (i : N.Inputs) :
  R.v44428 (state s) (inputs i) = Zmod.unsigned (N.v44428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44428 s i)) at 1.
  unfold R.v44428, N.v44428.
  unfold R.v6, N.v6.
  rewrite ?node_12093.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44429 (s : N.State) (i : N.Inputs) :
  R.v44429 (state s) (inputs i) = Zmod.unsigned (N.v44429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44429 s i)) at 1.
  unfold R.v44429, N.v44429.
  rewrite ?node_44426.
  rewrite ?node_44427.
  rewrite ?node_44428.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44430 (s : N.State) (i : N.Inputs) :
  R.v44430 (state s) (inputs i) = Zmod.unsigned (N.v44430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44430 s i)) at 1.
  unfold R.v44430, N.v44430.
  rewrite ?node_44425.
  rewrite ?node_44429.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44431 (s : N.State) (i : N.Inputs) :
  R.v44431 (state s) (inputs i) = Zmod.unsigned (N.v44431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44431 s i)) at 1.
  unfold R.v44431, N.v44431.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44432 (s : N.State) (i : N.Inputs) :
  R.v44432 (state s) (inputs i) = Zmod.unsigned (N.v44432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44432 s i)) at 1.
  unfold R.v44432, N.v44432.
  rewrite ?node_11895.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44433 (s : N.State) (i : N.Inputs) :
  R.v44433 (state s) (inputs i) = Zmod.unsigned (N.v44433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44433 s i)) at 1.
  unfold R.v44433, N.v44433.
  unfold R.v6, N.v6.
  rewrite ?node_11887.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44434 (s : N.State) (i : N.Inputs) :
  R.v44434 (state s) (inputs i) = Zmod.unsigned (N.v44434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44434 s i)) at 1.
  unfold R.v44434, N.v44434.
  unfold R.v6, N.v6.
  rewrite ?node_11880.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44435 (s : N.State) (i : N.Inputs) :
  R.v44435 (state s) (inputs i) = Zmod.unsigned (N.v44435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44435 s i)) at 1.
  unfold R.v44435, N.v44435.
  rewrite ?node_44433.
  rewrite ?node_44434.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44436 (s : N.State) (i : N.Inputs) :
  R.v44436 (state s) (inputs i) = Zmod.unsigned (N.v44436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44436 s i)) at 1.
  unfold R.v44436, N.v44436.
  unfold R.v16484, N.v16484.
  rewrite ?node_44435.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44437 (s : N.State) (i : N.Inputs) :
  R.v44437 (state s) (inputs i) = Zmod.unsigned (N.v44437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44437 s i)) at 1.
  unfold R.v44437, N.v44437.
  rewrite ?node_44432.
  rewrite ?node_44436.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44438 (s : N.State) (i : N.Inputs) :
  R.v44438 (state s) (inputs i) = Zmod.unsigned (N.v44438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44438 s i)) at 1.
  unfold R.v44438, N.v44438.
  unfold R.v6, N.v6.
  rewrite ?node_44437.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44439 (s : N.State) (i : N.Inputs) :
  R.v44439 (state s) (inputs i) = Zmod.unsigned (N.v44439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44439 s i)) at 1.
  unfold R.v44439, N.v44439.
  rewrite ?node_11896.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44440 (s : N.State) (i : N.Inputs) :
  R.v44440 (state s) (inputs i) = Zmod.unsigned (N.v44440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44440 s i)) at 1.
  unfold R.v44440, N.v44440.
  unfold R.v6, N.v6.
  rewrite ?node_12045.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44441 (s : N.State) (i : N.Inputs) :
  R.v44441 (state s) (inputs i) = Zmod.unsigned (N.v44441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44441 s i)) at 1.
  unfold R.v44441, N.v44441.
  rewrite ?node_44439.
  rewrite ?node_44440.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44442 (s : N.State) (i : N.Inputs) :
  R.v44442 (state s) (inputs i) = Zmod.unsigned (N.v44442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44442 s i)) at 1.
  unfold R.v44442, N.v44442.
  rewrite ?node_44438.
  rewrite ?node_44441.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44443 (s : N.State) (i : N.Inputs) :
  R.v44443 (state s) (inputs i) = Zmod.unsigned (N.v44443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44443 s i)) at 1.
  unfold R.v44443, N.v44443.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44444 (s : N.State) (i : N.Inputs) :
  R.v44444 (state s) (inputs i) = Zmod.unsigned (N.v44444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44444 s i)) at 1.
  unfold R.v44444, N.v44444.
  rewrite ?node_11900.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44445 (s : N.State) (i : N.Inputs) :
  R.v44445 (state s) (inputs i) = Zmod.unsigned (N.v44445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44445 s i)) at 1.
  unfold R.v44445, N.v44445.
  unfold R.v6, N.v6.
  rewrite !state_r1466_nr_5F1469.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1466_nr_5F1469 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44446 (s : N.State) (i : N.Inputs) :
  R.v44446 (state s) (inputs i) = Zmod.unsigned (N.v44446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44446 s i)) at 1.
  unfold R.v44446, N.v44446.
  unfold R.v6, N.v6.
  rewrite ?node_11896.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44447 (s : N.State) (i : N.Inputs) :
  R.v44447 (state s) (inputs i) = Zmod.unsigned (N.v44447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44447 s i)) at 1.
  unfold R.v44447, N.v44447.
  rewrite ?node_44445.
  rewrite ?node_44446.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44448 (s : N.State) (i : N.Inputs) :
  R.v44448 (state s) (inputs i) = Zmod.unsigned (N.v44448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44448 s i)) at 1.
  unfold R.v44448, N.v44448.
  unfold R.v16484, N.v16484.
  rewrite ?node_44447.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44449 (s : N.State) (i : N.Inputs) :
  R.v44449 (state s) (inputs i) = Zmod.unsigned (N.v44449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44449 s i)) at 1.
  unfold R.v44449, N.v44449.
  rewrite ?node_44444.
  rewrite ?node_44448.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44450 (s : N.State) (i : N.Inputs) :
  R.v44450 (state s) (inputs i) = Zmod.unsigned (N.v44450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44450 s i)) at 1.
  unfold R.v44450, N.v44450.
  unfold R.v6, N.v6.
  rewrite ?node_44449.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44451 (s : N.State) (i : N.Inputs) :
  R.v44451 (state s) (inputs i) = Zmod.unsigned (N.v44451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44451 s i)) at 1.
  unfold R.v44451, N.v44451.
  rewrite ?node_11901.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44452 (s : N.State) (i : N.Inputs) :
  R.v44452 (state s) (inputs i) = Zmod.unsigned (N.v44452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44452 s i)) at 1.
  unfold R.v44452, N.v44452.
  unfold R.v6, N.v6.
  rewrite ?node_12093.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44453 (s : N.State) (i : N.Inputs) :
  R.v44453 (state s) (inputs i) = Zmod.unsigned (N.v44453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44453 s i)) at 1.
  unfold R.v44453, N.v44453.
  rewrite ?node_44451.
  rewrite ?node_44452.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44454 (s : N.State) (i : N.Inputs) :
  R.v44454 (state s) (inputs i) = Zmod.unsigned (N.v44454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44454 s i)) at 1.
  unfold R.v44454, N.v44454.
  rewrite ?node_44450.
  rewrite ?node_44453.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44455 (s : N.State) (i : N.Inputs) :
  R.v44455 (state s) (inputs i) = Zmod.unsigned (N.v44455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44455 s i)) at 1.
  unfold R.v44455, N.v44455.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44456 (s : N.State) (i : N.Inputs) :
  R.v44456 (state s) (inputs i) = Zmod.unsigned (N.v44456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44456 s i)) at 1.
  unfold R.v44456, N.v44456.
  rewrite ?node_11920.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44457 (s : N.State) (i : N.Inputs) :
  R.v44457 (state s) (inputs i) = Zmod.unsigned (N.v44457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44457 s i)) at 1.
  unfold R.v44457, N.v44457.
  rewrite ?node_11916.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44458 (s : N.State) (i : N.Inputs) :
  R.v44458 (state s) (inputs i) = Zmod.unsigned (N.v44458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44458 s i)) at 1.
  unfold R.v44458, N.v44458.
  rewrite ?node_11912.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44459 (s : N.State) (i : N.Inputs) :
  R.v44459 (state s) (inputs i) = Zmod.unsigned (N.v44459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44459 s i)) at 1.
  unfold R.v44459, N.v44459.
  unfold R.v6, N.v6.
  rewrite ?node_11908.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44460 (s : N.State) (i : N.Inputs) :
  R.v44460 (state s) (inputs i) = Zmod.unsigned (N.v44460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44460 s i)) at 1.
  unfold R.v44460, N.v44460.
  unfold R.v6, N.v6.
  rewrite ?node_11905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44461 (s : N.State) (i : N.Inputs) :
  R.v44461 (state s) (inputs i) = Zmod.unsigned (N.v44461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44461 s i)) at 1.
  unfold R.v44461, N.v44461.
  rewrite ?node_44459.
  rewrite ?node_44460.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44462 (s : N.State) (i : N.Inputs) :
  R.v44462 (state s) (inputs i) = Zmod.unsigned (N.v44462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44462 s i)) at 1.
  unfold R.v44462, N.v44462.
  unfold R.v16484, N.v16484.
  rewrite ?node_44461.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44463 (s : N.State) (i : N.Inputs) :
  R.v44463 (state s) (inputs i) = Zmod.unsigned (N.v44463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44463 s i)) at 1.
  unfold R.v44463, N.v44463.
  rewrite ?node_44456.
  rewrite ?node_44457.
  rewrite ?node_44458.
  rewrite ?node_44462.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44464 (s : N.State) (i : N.Inputs) :
  R.v44464 (state s) (inputs i) = Zmod.unsigned (N.v44464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44464 s i)) at 1.
  unfold R.v44464, N.v44464.
  unfold R.v6, N.v6.
  rewrite ?node_44463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44465 (s : N.State) (i : N.Inputs) :
  R.v44465 (state s) (inputs i) = Zmod.unsigned (N.v44465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44465 s i)) at 1.
  unfold R.v44465, N.v44465.
  rewrite ?node_11921.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44466 (s : N.State) (i : N.Inputs) :
  R.v44466 (state s) (inputs i) = Zmod.unsigned (N.v44466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44466 s i)) at 1.
  unfold R.v44466, N.v44466.
  unfold R.v6, N.v6.
  rewrite ?node_12065.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44467 (s : N.State) (i : N.Inputs) :
  R.v44467 (state s) (inputs i) = Zmod.unsigned (N.v44467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44467 s i)) at 1.
  unfold R.v44467, N.v44467.
  unfold R.v6, N.v6.
  rewrite ?node_12097.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44468 (s : N.State) (i : N.Inputs) :
  R.v44468 (state s) (inputs i) = Zmod.unsigned (N.v44468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44468 s i)) at 1.
  unfold R.v44468, N.v44468.
  rewrite ?node_44465.
  rewrite ?node_44466.
  rewrite ?node_44467.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44469 (s : N.State) (i : N.Inputs) :
  R.v44469 (state s) (inputs i) = Zmod.unsigned (N.v44469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44469 s i)) at 1.
  unfold R.v44469, N.v44469.
  rewrite ?node_44464.
  rewrite ?node_44468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44470 (s : N.State) (i : N.Inputs) :
  R.v44470 (state s) (inputs i) = Zmod.unsigned (N.v44470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44470 s i)) at 1.
  unfold R.v44470, N.v44470.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44471 (s : N.State) (i : N.Inputs) :
  R.v44471 (state s) (inputs i) = Zmod.unsigned (N.v44471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44471 s i)) at 1.
  unfold R.v44471, N.v44471.
  rewrite ?node_11912.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44472 (s : N.State) (i : N.Inputs) :
  R.v44472 (state s) (inputs i) = Zmod.unsigned (N.v44472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44472 s i)) at 1.
  unfold R.v44472, N.v44472.
  unfold R.v6, N.v6.
  rewrite ?node_11908.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44473 (s : N.State) (i : N.Inputs) :
  R.v44473 (state s) (inputs i) = Zmod.unsigned (N.v44473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44473 s i)) at 1.
  unfold R.v44473, N.v44473.
  unfold R.v6, N.v6.
  rewrite ?node_11905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44474 (s : N.State) (i : N.Inputs) :
  R.v44474 (state s) (inputs i) = Zmod.unsigned (N.v44474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44474 s i)) at 1.
  unfold R.v44474, N.v44474.
  rewrite ?node_44472.
  rewrite ?node_44473.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44475 (s : N.State) (i : N.Inputs) :
  R.v44475 (state s) (inputs i) = Zmod.unsigned (N.v44475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44475 s i)) at 1.
  unfold R.v44475, N.v44475.
  unfold R.v16484, N.v16484.
  rewrite ?node_44474.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44476 (s : N.State) (i : N.Inputs) :
  R.v44476 (state s) (inputs i) = Zmod.unsigned (N.v44476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44476 s i)) at 1.
  unfold R.v44476, N.v44476.
  rewrite ?node_44471.
  rewrite ?node_44475.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44477 (s : N.State) (i : N.Inputs) :
  R.v44477 (state s) (inputs i) = Zmod.unsigned (N.v44477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44477 s i)) at 1.
  unfold R.v44477, N.v44477.
  unfold R.v6, N.v6.
  rewrite ?node_44476.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44478 (s : N.State) (i : N.Inputs) :
  R.v44478 (state s) (inputs i) = Zmod.unsigned (N.v44478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44478 s i)) at 1.
  unfold R.v44478, N.v44478.
  rewrite ?node_11913.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44479 (s : N.State) (i : N.Inputs) :
  R.v44479 (state s) (inputs i) = Zmod.unsigned (N.v44479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44479 s i)) at 1.
  unfold R.v44479, N.v44479.
  unfold R.v6, N.v6.
  rewrite ?node_12065.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44480 (s : N.State) (i : N.Inputs) :
  R.v44480 (state s) (inputs i) = Zmod.unsigned (N.v44480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44480 s i)) at 1.
  unfold R.v44480, N.v44480.
  rewrite ?node_44478.
  rewrite ?node_44479.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44481 (s : N.State) (i : N.Inputs) :
  R.v44481 (state s) (inputs i) = Zmod.unsigned (N.v44481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44481 s i)) at 1.
  unfold R.v44481, N.v44481.
  rewrite ?node_44477.
  rewrite ?node_44480.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44482 (s : N.State) (i : N.Inputs) :
  R.v44482 (state s) (inputs i) = Zmod.unsigned (N.v44482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44482 s i)) at 1.
  unfold R.v44482, N.v44482.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44483 (s : N.State) (i : N.Inputs) :
  R.v44483 (state s) (inputs i) = Zmod.unsigned (N.v44483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44483 s i)) at 1.
  unfold R.v44483, N.v44483.
  rewrite ?node_11920.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44484 (s : N.State) (i : N.Inputs) :
  R.v44484 (state s) (inputs i) = Zmod.unsigned (N.v44484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44484 s i)) at 1.
  unfold R.v44484, N.v44484.
  unfold R.v6, N.v6.
  rewrite ?node_11916.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44485 (s : N.State) (i : N.Inputs) :
  R.v44485 (state s) (inputs i) = Zmod.unsigned (N.v44485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44485 s i)) at 1.
  unfold R.v44485, N.v44485.
  unfold R.v6, N.v6.
  rewrite ?node_11913.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44486 (s : N.State) (i : N.Inputs) :
  R.v44486 (state s) (inputs i) = Zmod.unsigned (N.v44486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44486 s i)) at 1.
  unfold R.v44486, N.v44486.
  rewrite ?node_44484.
  rewrite ?node_44485.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44487 (s : N.State) (i : N.Inputs) :
  R.v44487 (state s) (inputs i) = Zmod.unsigned (N.v44487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44487 s i)) at 1.
  unfold R.v44487, N.v44487.
  unfold R.v16484, N.v16484.
  rewrite ?node_44486.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44488 (s : N.State) (i : N.Inputs) :
  R.v44488 (state s) (inputs i) = Zmod.unsigned (N.v44488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44488 s i)) at 1.
  unfold R.v44488, N.v44488.
  rewrite ?node_44483.
  rewrite ?node_44487.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44489 (s : N.State) (i : N.Inputs) :
  R.v44489 (state s) (inputs i) = Zmod.unsigned (N.v44489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44489 s i)) at 1.
  unfold R.v44489, N.v44489.
  unfold R.v6, N.v6.
  rewrite ?node_44488.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44490 (s : N.State) (i : N.Inputs) :
  R.v44490 (state s) (inputs i) = Zmod.unsigned (N.v44490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44490 s i)) at 1.
  unfold R.v44490, N.v44490.
  rewrite ?node_11921.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44491 (s : N.State) (i : N.Inputs) :
  R.v44491 (state s) (inputs i) = Zmod.unsigned (N.v44491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44491 s i)) at 1.
  unfold R.v44491, N.v44491.
  unfold R.v6, N.v6.
  rewrite ?node_12097.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44492 (s : N.State) (i : N.Inputs) :
  R.v44492 (state s) (inputs i) = Zmod.unsigned (N.v44492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44492 s i)) at 1.
  unfold R.v44492, N.v44492.
  rewrite ?node_44490.
  rewrite ?node_44491.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44493 (s : N.State) (i : N.Inputs) :
  R.v44493 (state s) (inputs i) = Zmod.unsigned (N.v44493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44493 s i)) at 1.
  unfold R.v44493, N.v44493.
  rewrite ?node_44489.
  rewrite ?node_44492.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44494 (s : N.State) (i : N.Inputs) :
  R.v44494 (state s) (inputs i) = Zmod.unsigned (N.v44494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44494 s i)) at 1.
  unfold R.v44494, N.v44494.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44495 (s : N.State) (i : N.Inputs) :
  R.v44495 (state s) (inputs i) = Zmod.unsigned (N.v44495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44495 s i)) at 1.
  unfold R.v44495, N.v44495.
  rewrite ?node_11938.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44496 (s : N.State) (i : N.Inputs) :
  R.v44496 (state s) (inputs i) = Zmod.unsigned (N.v44496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44496 s i)) at 1.
  unfold R.v44496, N.v44496.
  rewrite ?node_11934.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44497 (s : N.State) (i : N.Inputs) :
  R.v44497 (state s) (inputs i) = Zmod.unsigned (N.v44497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44497 s i)) at 1.
  unfold R.v44497, N.v44497.
  rewrite ?node_11932.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44498 (s : N.State) (i : N.Inputs) :
  R.v44498 (state s) (inputs i) = Zmod.unsigned (N.v44498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44498 s i)) at 1.
  unfold R.v44498, N.v44498.
  unfold R.v6, N.v6.
  rewrite ?node_11928.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44499 (s : N.State) (i : N.Inputs) :
  R.v44499 (state s) (inputs i) = Zmod.unsigned (N.v44499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44499 s i)) at 1.
  unfold R.v44499, N.v44499.
  unfold R.v6, N.v6.
  rewrite ?node_11925.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44500 (s : N.State) (i : N.Inputs) :
  R.v44500 (state s) (inputs i) = Zmod.unsigned (N.v44500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44500 s i)) at 1.
  unfold R.v44500, N.v44500.
  rewrite ?node_44498.
  rewrite ?node_44499.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44501 (s : N.State) (i : N.Inputs) :
  R.v44501 (state s) (inputs i) = Zmod.unsigned (N.v44501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44501 s i)) at 1.
  unfold R.v44501, N.v44501.
  unfold R.v16484, N.v16484.
  rewrite ?node_44500.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44502 (s : N.State) (i : N.Inputs) :
  R.v44502 (state s) (inputs i) = Zmod.unsigned (N.v44502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44502 s i)) at 1.
  unfold R.v44502, N.v44502.
  rewrite ?node_44495.
  rewrite ?node_44496.
  rewrite ?node_44497.
  rewrite ?node_44501.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44503 (s : N.State) (i : N.Inputs) :
  R.v44503 (state s) (inputs i) = Zmod.unsigned (N.v44503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44503 s i)) at 1.
  unfold R.v44503, N.v44503.
  unfold R.v6, N.v6.
  rewrite ?node_44502.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44504 (s : N.State) (i : N.Inputs) :
  R.v44504 (state s) (inputs i) = Zmod.unsigned (N.v44504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44504 s i)) at 1.
  unfold R.v44504, N.v44504.
  rewrite ?node_11939.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44505 (s : N.State) (i : N.Inputs) :
  R.v44505 (state s) (inputs i) = Zmod.unsigned (N.v44505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44505 s i)) at 1.
  unfold R.v44505, N.v44505.
  unfold R.v6, N.v6.
  rewrite ?node_12086.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44506 (s : N.State) (i : N.Inputs) :
  R.v44506 (state s) (inputs i) = Zmod.unsigned (N.v44506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44506 s i)) at 1.
  unfold R.v44506, N.v44506.
  unfold R.v6, N.v6.
  rewrite ?node_12106.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44507 (s : N.State) (i : N.Inputs) :
  R.v44507 (state s) (inputs i) = Zmod.unsigned (N.v44507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44507 s i)) at 1.
  unfold R.v44507, N.v44507.
  rewrite ?node_44504.
  rewrite ?node_44505.
  rewrite ?node_44506.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44508 (s : N.State) (i : N.Inputs) :
  R.v44508 (state s) (inputs i) = Zmod.unsigned (N.v44508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44508 s i)) at 1.
  unfold R.v44508, N.v44508.
  rewrite ?node_44503.
  rewrite ?node_44507.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44509 (s : N.State) (i : N.Inputs) :
  R.v44509 (state s) (inputs i) = Zmod.unsigned (N.v44509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44509 s i)) at 1.
  unfold R.v44509, N.v44509.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44510 (s : N.State) (i : N.Inputs) :
  R.v44510 (state s) (inputs i) = Zmod.unsigned (N.v44510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44510 s i)) at 1.
  unfold R.v44510, N.v44510.
  rewrite ?node_11932.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44511 (s : N.State) (i : N.Inputs) :
  R.v44511 (state s) (inputs i) = Zmod.unsigned (N.v44511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44511 s i)) at 1.
  unfold R.v44511, N.v44511.
  unfold R.v6, N.v6.
  rewrite ?node_11928.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44512 (s : N.State) (i : N.Inputs) :
  R.v44512 (state s) (inputs i) = Zmod.unsigned (N.v44512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44512 s i)) at 1.
  unfold R.v44512, N.v44512.
  unfold R.v6, N.v6.
  rewrite ?node_11925.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44513 (s : N.State) (i : N.Inputs) :
  R.v44513 (state s) (inputs i) = Zmod.unsigned (N.v44513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44513 s i)) at 1.
  unfold R.v44513, N.v44513.
  rewrite ?node_44511.
  rewrite ?node_44512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44514 (s : N.State) (i : N.Inputs) :
  R.v44514 (state s) (inputs i) = Zmod.unsigned (N.v44514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44514 s i)) at 1.
  unfold R.v44514, N.v44514.
  unfold R.v16484, N.v16484.
  rewrite ?node_44513.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44515 (s : N.State) (i : N.Inputs) :
  R.v44515 (state s) (inputs i) = Zmod.unsigned (N.v44515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44515 s i)) at 1.
  unfold R.v44515, N.v44515.
  rewrite ?node_44510.
  rewrite ?node_44514.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44516 (s : N.State) (i : N.Inputs) :
  R.v44516 (state s) (inputs i) = Zmod.unsigned (N.v44516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44516 s i)) at 1.
  unfold R.v44516, N.v44516.
  unfold R.v6, N.v6.
  rewrite ?node_44515.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44517 (s : N.State) (i : N.Inputs) :
  R.v44517 (state s) (inputs i) = Zmod.unsigned (N.v44517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44517 s i)) at 1.
  unfold R.v44517, N.v44517.
  rewrite ?node_11933.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44518 (s : N.State) (i : N.Inputs) :
  R.v44518 (state s) (inputs i) = Zmod.unsigned (N.v44518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44518 s i)) at 1.
  unfold R.v44518, N.v44518.
  unfold R.v6, N.v6.
  rewrite ?node_12086.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44519 (s : N.State) (i : N.Inputs) :
  R.v44519 (state s) (inputs i) = Zmod.unsigned (N.v44519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44519 s i)) at 1.
  unfold R.v44519, N.v44519.
  rewrite ?node_44517.
  rewrite ?node_44518.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44520 (s : N.State) (i : N.Inputs) :
  R.v44520 (state s) (inputs i) = Zmod.unsigned (N.v44520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44520 s i)) at 1.
  unfold R.v44520, N.v44520.
  rewrite ?node_44516.
  rewrite ?node_44519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44521 (s : N.State) (i : N.Inputs) :
  R.v44521 (state s) (inputs i) = Zmod.unsigned (N.v44521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44521 s i)) at 1.
  unfold R.v44521, N.v44521.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44522 (s : N.State) (i : N.Inputs) :
  R.v44522 (state s) (inputs i) = Zmod.unsigned (N.v44522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44522 s i)) at 1.
  unfold R.v44522, N.v44522.
  rewrite ?node_11938.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44523 (s : N.State) (i : N.Inputs) :
  R.v44523 (state s) (inputs i) = Zmod.unsigned (N.v44523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44523 s i)) at 1.
  unfold R.v44523, N.v44523.
  unfold R.v6, N.v6.
  rewrite ?node_11934.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44524 (s : N.State) (i : N.Inputs) :
  R.v44524 (state s) (inputs i) = Zmod.unsigned (N.v44524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44524 s i)) at 1.
  unfold R.v44524, N.v44524.
  unfold R.v6, N.v6.
  rewrite ?node_11933.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44525 (s : N.State) (i : N.Inputs) :
  R.v44525 (state s) (inputs i) = Zmod.unsigned (N.v44525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44525 s i)) at 1.
  unfold R.v44525, N.v44525.
  rewrite ?node_44523.
  rewrite ?node_44524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44526 (s : N.State) (i : N.Inputs) :
  R.v44526 (state s) (inputs i) = Zmod.unsigned (N.v44526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44526 s i)) at 1.
  unfold R.v44526, N.v44526.
  unfold R.v16484, N.v16484.
  rewrite ?node_44525.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44527 (s : N.State) (i : N.Inputs) :
  R.v44527 (state s) (inputs i) = Zmod.unsigned (N.v44527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44527 s i)) at 1.
  unfold R.v44527, N.v44527.
  rewrite ?node_44522.
  rewrite ?node_44526.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44528 (s : N.State) (i : N.Inputs) :
  R.v44528 (state s) (inputs i) = Zmod.unsigned (N.v44528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44528 s i)) at 1.
  unfold R.v44528, N.v44528.
  unfold R.v6, N.v6.
  rewrite ?node_44527.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44529 (s : N.State) (i : N.Inputs) :
  R.v44529 (state s) (inputs i) = Zmod.unsigned (N.v44529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44529 s i)) at 1.
  unfold R.v44529, N.v44529.
  rewrite ?node_11939.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44530 (s : N.State) (i : N.Inputs) :
  R.v44530 (state s) (inputs i) = Zmod.unsigned (N.v44530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44530 s i)) at 1.
  unfold R.v44530, N.v44530.
  unfold R.v6, N.v6.
  rewrite ?node_12106.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44531 (s : N.State) (i : N.Inputs) :
  R.v44531 (state s) (inputs i) = Zmod.unsigned (N.v44531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44531 s i)) at 1.
  unfold R.v44531, N.v44531.
  rewrite ?node_44529.
  rewrite ?node_44530.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44532 (s : N.State) (i : N.Inputs) :
  R.v44532 (state s) (inputs i) = Zmod.unsigned (N.v44532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44532 s i)) at 1.
  unfold R.v44532, N.v44532.
  rewrite ?node_44528.
  rewrite ?node_44531.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44533 (s : N.State) (i : N.Inputs) :
  R.v44533 (state s) (inputs i) = Zmod.unsigned (N.v44533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44533 s i)) at 1.
  unfold R.v44533, N.v44533.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44534 (s : N.State) (i : N.Inputs) :
  R.v44534 (state s) (inputs i) = Zmod.unsigned (N.v44534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44534 s i)) at 1.
  unfold R.v44534, N.v44534.
  rewrite ?node_12017.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44535 (s : N.State) (i : N.Inputs) :
  R.v44535 (state s) (inputs i) = Zmod.unsigned (N.v44535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44535 s i)) at 1.
  unfold R.v44535, N.v44535.
  rewrite ?node_12013.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44536 (s : N.State) (i : N.Inputs) :
  R.v44536 (state s) (inputs i) = Zmod.unsigned (N.v44536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44536 s i)) at 1.
  unfold R.v44536, N.v44536.
  rewrite ?node_12005.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44537 (s : N.State) (i : N.Inputs) :
  R.v44537 (state s) (inputs i) = Zmod.unsigned (N.v44537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44537 s i)) at 1.
  unfold R.v44537, N.v44537.
  unfold R.v6, N.v6.
  rewrite ?node_11997.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44538 (s : N.State) (i : N.Inputs) :
  R.v44538 (state s) (inputs i) = Zmod.unsigned (N.v44538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44538 s i)) at 1.
  unfold R.v44538, N.v44538.
  unfold R.v6, N.v6.
  rewrite ?node_11990.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44539 (s : N.State) (i : N.Inputs) :
  R.v44539 (state s) (inputs i) = Zmod.unsigned (N.v44539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44539 s i)) at 1.
  unfold R.v44539, N.v44539.
  rewrite ?node_44537.
  rewrite ?node_44538.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44540 (s : N.State) (i : N.Inputs) :
  R.v44540 (state s) (inputs i) = Zmod.unsigned (N.v44540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44540 s i)) at 1.
  unfold R.v44540, N.v44540.
  unfold R.v16484, N.v16484.
  rewrite ?node_44539.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44541 (s : N.State) (i : N.Inputs) :
  R.v44541 (state s) (inputs i) = Zmod.unsigned (N.v44541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44541 s i)) at 1.
  unfold R.v44541, N.v44541.
  rewrite ?node_44534.
  rewrite ?node_44535.
  rewrite ?node_44536.
  rewrite ?node_44540.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44542 (s : N.State) (i : N.Inputs) :
  R.v44542 (state s) (inputs i) = Zmod.unsigned (N.v44542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44542 s i)) at 1.
  unfold R.v44542, N.v44542.
  unfold R.v6, N.v6.
  rewrite ?node_44541.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44543 (s : N.State) (i : N.Inputs) :
  R.v44543 (state s) (inputs i) = Zmod.unsigned (N.v44543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44543 s i)) at 1.
  unfold R.v44543, N.v44543.
  rewrite ?node_12018.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44544 (s : N.State) (i : N.Inputs) :
  R.v44544 (state s) (inputs i) = Zmod.unsigned (N.v44544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44544 s i)) at 1.
  unfold R.v44544, N.v44544.
  unfold R.v6, N.v6.
  rewrite ?node_12159.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44545 (s : N.State) (i : N.Inputs) :
  R.v44545 (state s) (inputs i) = Zmod.unsigned (N.v44545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44545 s i)) at 1.
  unfold R.v44545, N.v44545.
  unfold R.v6, N.v6.
  rewrite ?node_12227.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44546 (s : N.State) (i : N.Inputs) :
  R.v44546 (state s) (inputs i) = Zmod.unsigned (N.v44546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44546 s i)) at 1.
  unfold R.v44546, N.v44546.
  rewrite ?node_44543.
  rewrite ?node_44544.
  rewrite ?node_44545.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44547 (s : N.State) (i : N.Inputs) :
  R.v44547 (state s) (inputs i) = Zmod.unsigned (N.v44547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44547 s i)) at 1.
  unfold R.v44547, N.v44547.
  rewrite ?node_44542.
  rewrite ?node_44546.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44548 (s : N.State) (i : N.Inputs) :
  R.v44548 (state s) (inputs i) = Zmod.unsigned (N.v44548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44548 s i)) at 1.
  unfold R.v44548, N.v44548.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44549 (s : N.State) (i : N.Inputs) :
  R.v44549 (state s) (inputs i) = Zmod.unsigned (N.v44549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44549 s i)) at 1.
  unfold R.v44549, N.v44549.
  rewrite ?node_12005.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44550 (s : N.State) (i : N.Inputs) :
  R.v44550 (state s) (inputs i) = Zmod.unsigned (N.v44550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44550 s i)) at 1.
  unfold R.v44550, N.v44550.
  unfold R.v6, N.v6.
  rewrite ?node_11997.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44551 (s : N.State) (i : N.Inputs) :
  R.v44551 (state s) (inputs i) = Zmod.unsigned (N.v44551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44551 s i)) at 1.
  unfold R.v44551, N.v44551.
  unfold R.v6, N.v6.
  rewrite ?node_11990.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44552 (s : N.State) (i : N.Inputs) :
  R.v44552 (state s) (inputs i) = Zmod.unsigned (N.v44552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44552 s i)) at 1.
  unfold R.v44552, N.v44552.
  rewrite ?node_44550.
  rewrite ?node_44551.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44553 (s : N.State) (i : N.Inputs) :
  R.v44553 (state s) (inputs i) = Zmod.unsigned (N.v44553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44553 s i)) at 1.
  unfold R.v44553, N.v44553.
  unfold R.v16484, N.v16484.
  rewrite ?node_44552.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44554 (s : N.State) (i : N.Inputs) :
  R.v44554 (state s) (inputs i) = Zmod.unsigned (N.v44554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44554 s i)) at 1.
  unfold R.v44554, N.v44554.
  rewrite ?node_44549.
  rewrite ?node_44553.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44555 (s : N.State) (i : N.Inputs) :
  R.v44555 (state s) (inputs i) = Zmod.unsigned (N.v44555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44555 s i)) at 1.
  unfold R.v44555, N.v44555.
  unfold R.v6, N.v6.
  rewrite ?node_44554.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44556 (s : N.State) (i : N.Inputs) :
  R.v44556 (state s) (inputs i) = Zmod.unsigned (N.v44556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44556 s i)) at 1.
  unfold R.v44556, N.v44556.
  rewrite ?node_12006.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44557 (s : N.State) (i : N.Inputs) :
  R.v44557 (state s) (inputs i) = Zmod.unsigned (N.v44557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44557 s i)) at 1.
  unfold R.v44557, N.v44557.
  unfold R.v6, N.v6.
  rewrite ?node_12159.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44558 (s : N.State) (i : N.Inputs) :
  R.v44558 (state s) (inputs i) = Zmod.unsigned (N.v44558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44558 s i)) at 1.
  unfold R.v44558, N.v44558.
  rewrite ?node_44556.
  rewrite ?node_44557.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44559 (s : N.State) (i : N.Inputs) :
  R.v44559 (state s) (inputs i) = Zmod.unsigned (N.v44559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44559 s i)) at 1.
  unfold R.v44559, N.v44559.
  rewrite ?node_44555.
  rewrite ?node_44558.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44560 (s : N.State) (i : N.Inputs) :
  R.v44560 (state s) (inputs i) = Zmod.unsigned (N.v44560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44560 s i)) at 1.
  unfold R.v44560, N.v44560.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44561 (s : N.State) (i : N.Inputs) :
  R.v44561 (state s) (inputs i) = Zmod.unsigned (N.v44561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44561 s i)) at 1.
  unfold R.v44561, N.v44561.
  rewrite ?node_12017.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44562 (s : N.State) (i : N.Inputs) :
  R.v44562 (state s) (inputs i) = Zmod.unsigned (N.v44562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44562 s i)) at 1.
  unfold R.v44562, N.v44562.
  unfold R.v6, N.v6.
  rewrite ?node_12013.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44563 (s : N.State) (i : N.Inputs) :
  R.v44563 (state s) (inputs i) = Zmod.unsigned (N.v44563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44563 s i)) at 1.
  unfold R.v44563, N.v44563.
  unfold R.v6, N.v6.
  rewrite ?node_12006.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44564 (s : N.State) (i : N.Inputs) :
  R.v44564 (state s) (inputs i) = Zmod.unsigned (N.v44564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44564 s i)) at 1.
  unfold R.v44564, N.v44564.
  rewrite ?node_44562.
  rewrite ?node_44563.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44565 (s : N.State) (i : N.Inputs) :
  R.v44565 (state s) (inputs i) = Zmod.unsigned (N.v44565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44565 s i)) at 1.
  unfold R.v44565, N.v44565.
  unfold R.v16484, N.v16484.
  rewrite ?node_44564.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44566 (s : N.State) (i : N.Inputs) :
  R.v44566 (state s) (inputs i) = Zmod.unsigned (N.v44566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44566 s i)) at 1.
  unfold R.v44566, N.v44566.
  rewrite ?node_44561.
  rewrite ?node_44565.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44567 (s : N.State) (i : N.Inputs) :
  R.v44567 (state s) (inputs i) = Zmod.unsigned (N.v44567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44567 s i)) at 1.
  unfold R.v44567, N.v44567.
  unfold R.v6, N.v6.
  rewrite ?node_44566.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44568 (s : N.State) (i : N.Inputs) :
  R.v44568 (state s) (inputs i) = Zmod.unsigned (N.v44568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44568 s i)) at 1.
  unfold R.v44568, N.v44568.
  rewrite ?node_12018.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44569 (s : N.State) (i : N.Inputs) :
  R.v44569 (state s) (inputs i) = Zmod.unsigned (N.v44569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44569 s i)) at 1.
  unfold R.v44569, N.v44569.
  unfold R.v6, N.v6.
  rewrite ?node_12227.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44570 (s : N.State) (i : N.Inputs) :
  R.v44570 (state s) (inputs i) = Zmod.unsigned (N.v44570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44570 s i)) at 1.
  unfold R.v44570, N.v44570.
  rewrite ?node_44568.
  rewrite ?node_44569.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44571 (s : N.State) (i : N.Inputs) :
  R.v44571 (state s) (inputs i) = Zmod.unsigned (N.v44571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44571 s i)) at 1.
  unfold R.v44571, N.v44571.
  rewrite ?node_44567.
  rewrite ?node_44570.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44572 (s : N.State) (i : N.Inputs) :
  R.v44572 (state s) (inputs i) = Zmod.unsigned (N.v44572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44572 s i)) at 1.
  unfold R.v44572, N.v44572.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44573 (s : N.State) (i : N.Inputs) :
  R.v44573 (state s) (inputs i) = Zmod.unsigned (N.v44573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44573 s i)) at 1.
  unfold R.v44573, N.v44573.
  rewrite ?node_12045.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44574 (s : N.State) (i : N.Inputs) :
  R.v44574 (state s) (inputs i) = Zmod.unsigned (N.v44574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44574 s i)) at 1.
  unfold R.v44574, N.v44574.
  unfold R.v16463, N.v16463.
  rewrite !state_r1494_nr_5F1498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1494_nr_5F1498 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44575 (s : N.State) (i : N.Inputs) :
  R.v44575 (state s) (inputs i) = Zmod.unsigned (N.v44575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44575 s i)) at 1.
  unfold R.v44575, N.v44575.
  rewrite ?node_12040.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44576 (s : N.State) (i : N.Inputs) :
  R.v44576 (state s) (inputs i) = Zmod.unsigned (N.v44576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44576 s i)) at 1.
  unfold R.v44576, N.v44576.
  unfold R.v6, N.v6.
  rewrite ?node_12032.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44577 (s : N.State) (i : N.Inputs) :
  R.v44577 (state s) (inputs i) = Zmod.unsigned (N.v44577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44577 s i)) at 1.
  unfold R.v44577, N.v44577.
  unfold R.v6, N.v6.
  rewrite ?node_12025.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44578 (s : N.State) (i : N.Inputs) :
  R.v44578 (state s) (inputs i) = Zmod.unsigned (N.v44578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44578 s i)) at 1.
  unfold R.v44578, N.v44578.
  rewrite ?node_44576.
  rewrite ?node_44577.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44579 (s : N.State) (i : N.Inputs) :
  R.v44579 (state s) (inputs i) = Zmod.unsigned (N.v44579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44579 s i)) at 1.
  unfold R.v44579, N.v44579.
  unfold R.v16484, N.v16484.
  rewrite ?node_44578.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44580 (s : N.State) (i : N.Inputs) :
  R.v44580 (state s) (inputs i) = Zmod.unsigned (N.v44580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44580 s i)) at 1.
  unfold R.v44580, N.v44580.
  rewrite ?node_44573.
  rewrite ?node_44574.
  rewrite ?node_44575.
  rewrite ?node_44579.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44581 (s : N.State) (i : N.Inputs) :
  R.v44581 (state s) (inputs i) = Zmod.unsigned (N.v44581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44581 s i)) at 1.
  unfold R.v44581, N.v44581.
  unfold R.v6, N.v6.
  rewrite ?node_44580.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44582 (s : N.State) (i : N.Inputs) :
  R.v44582 (state s) (inputs i) = Zmod.unsigned (N.v44582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44582 s i)) at 1.
  unfold R.v44582, N.v44582.
  rewrite ?node_12046.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44583 (s : N.State) (i : N.Inputs) :
  R.v44583 (state s) (inputs i) = Zmod.unsigned (N.v44583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44583 s i)) at 1.
  unfold R.v44583, N.v44583.
  unfold R.v6, N.v6.
  rewrite ?node_12190.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44584 (s : N.State) (i : N.Inputs) :
  R.v44584 (state s) (inputs i) = Zmod.unsigned (N.v44584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44584 s i)) at 1.
  unfold R.v44584, N.v44584.
  unfold R.v6, N.v6.
  rewrite ?node_12230.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44585 (s : N.State) (i : N.Inputs) :
  R.v44585 (state s) (inputs i) = Zmod.unsigned (N.v44585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44585 s i)) at 1.
  unfold R.v44585, N.v44585.
  rewrite ?node_44582.
  rewrite ?node_44583.
  rewrite ?node_44584.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44586 (s : N.State) (i : N.Inputs) :
  R.v44586 (state s) (inputs i) = Zmod.unsigned (N.v44586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44586 s i)) at 1.
  unfold R.v44586, N.v44586.
  rewrite ?node_44581.
  rewrite ?node_44585.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44587 (s : N.State) (i : N.Inputs) :
  R.v44587 (state s) (inputs i) = Zmod.unsigned (N.v44587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44587 s i)) at 1.
  unfold R.v44587, N.v44587.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44588 (s : N.State) (i : N.Inputs) :
  R.v44588 (state s) (inputs i) = Zmod.unsigned (N.v44588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44588 s i)) at 1.
  unfold R.v44588, N.v44588.
  rewrite ?node_12040.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44589 (s : N.State) (i : N.Inputs) :
  R.v44589 (state s) (inputs i) = Zmod.unsigned (N.v44589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44589 s i)) at 1.
  unfold R.v44589, N.v44589.
  unfold R.v6, N.v6.
  rewrite ?node_12032.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44590 (s : N.State) (i : N.Inputs) :
  R.v44590 (state s) (inputs i) = Zmod.unsigned (N.v44590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44590 s i)) at 1.
  unfold R.v44590, N.v44590.
  unfold R.v6, N.v6.
  rewrite ?node_12025.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44591 (s : N.State) (i : N.Inputs) :
  R.v44591 (state s) (inputs i) = Zmod.unsigned (N.v44591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44591 s i)) at 1.
  unfold R.v44591, N.v44591.
  rewrite ?node_44589.
  rewrite ?node_44590.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44592 (s : N.State) (i : N.Inputs) :
  R.v44592 (state s) (inputs i) = Zmod.unsigned (N.v44592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44592 s i)) at 1.
  unfold R.v44592, N.v44592.
  unfold R.v16484, N.v16484.
  rewrite ?node_44591.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44593 (s : N.State) (i : N.Inputs) :
  R.v44593 (state s) (inputs i) = Zmod.unsigned (N.v44593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44593 s i)) at 1.
  unfold R.v44593, N.v44593.
  rewrite ?node_44588.
  rewrite ?node_44592.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44594 (s : N.State) (i : N.Inputs) :
  R.v44594 (state s) (inputs i) = Zmod.unsigned (N.v44594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44594 s i)) at 1.
  unfold R.v44594, N.v44594.
  unfold R.v6, N.v6.
  rewrite ?node_44593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44595 (s : N.State) (i : N.Inputs) :
  R.v44595 (state s) (inputs i) = Zmod.unsigned (N.v44595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44595 s i)) at 1.
  unfold R.v44595, N.v44595.
  rewrite ?node_12041.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44596 (s : N.State) (i : N.Inputs) :
  R.v44596 (state s) (inputs i) = Zmod.unsigned (N.v44596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44596 s i)) at 1.
  unfold R.v44596, N.v44596.
  unfold R.v6, N.v6.
  rewrite ?node_12190.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44597 (s : N.State) (i : N.Inputs) :
  R.v44597 (state s) (inputs i) = Zmod.unsigned (N.v44597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44597 s i)) at 1.
  unfold R.v44597, N.v44597.
  rewrite ?node_44595.
  rewrite ?node_44596.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44598 (s : N.State) (i : N.Inputs) :
  R.v44598 (state s) (inputs i) = Zmod.unsigned (N.v44598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44598 s i)) at 1.
  unfold R.v44598, N.v44598.
  rewrite ?node_44594.
  rewrite ?node_44597.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44599 (s : N.State) (i : N.Inputs) :
  R.v44599 (state s) (inputs i) = Zmod.unsigned (N.v44599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44599 s i)) at 1.
  unfold R.v44599, N.v44599.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44600 (s : N.State) (i : N.Inputs) :
  R.v44600 (state s) (inputs i) = Zmod.unsigned (N.v44600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44600 s i)) at 1.
  unfold R.v44600, N.v44600.
  rewrite ?node_12045.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44601 (s : N.State) (i : N.Inputs) :
  R.v44601 (state s) (inputs i) = Zmod.unsigned (N.v44601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44601 s i)) at 1.
  unfold R.v44601, N.v44601.
  unfold R.v6, N.v6.
  rewrite !state_r1494_nr_5F1498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1494_nr_5F1498 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44602 (s : N.State) (i : N.Inputs) :
  R.v44602 (state s) (inputs i) = Zmod.unsigned (N.v44602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44602 s i)) at 1.
  unfold R.v44602, N.v44602.
  unfold R.v6, N.v6.
  rewrite ?node_12041.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44603 (s : N.State) (i : N.Inputs) :
  R.v44603 (state s) (inputs i) = Zmod.unsigned (N.v44603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44603 s i)) at 1.
  unfold R.v44603, N.v44603.
  rewrite ?node_44601.
  rewrite ?node_44602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44604 (s : N.State) (i : N.Inputs) :
  R.v44604 (state s) (inputs i) = Zmod.unsigned (N.v44604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44604 s i)) at 1.
  unfold R.v44604, N.v44604.
  unfold R.v16484, N.v16484.
  rewrite ?node_44603.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44605 (s : N.State) (i : N.Inputs) :
  R.v44605 (state s) (inputs i) = Zmod.unsigned (N.v44605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44605 s i)) at 1.
  unfold R.v44605, N.v44605.
  rewrite ?node_44600.
  rewrite ?node_44604.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44606 (s : N.State) (i : N.Inputs) :
  R.v44606 (state s) (inputs i) = Zmod.unsigned (N.v44606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44606 s i)) at 1.
  unfold R.v44606, N.v44606.
  unfold R.v6, N.v6.
  rewrite ?node_44605.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44607 (s : N.State) (i : N.Inputs) :
  R.v44607 (state s) (inputs i) = Zmod.unsigned (N.v44607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44607 s i)) at 1.
  unfold R.v44607, N.v44607.
  rewrite ?node_12046.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44608 (s : N.State) (i : N.Inputs) :
  R.v44608 (state s) (inputs i) = Zmod.unsigned (N.v44608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44608 s i)) at 1.
  unfold R.v44608, N.v44608.
  unfold R.v6, N.v6.
  rewrite ?node_12230.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44609 (s : N.State) (i : N.Inputs) :
  R.v44609 (state s) (inputs i) = Zmod.unsigned (N.v44609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44609 s i)) at 1.
  unfold R.v44609, N.v44609.
  rewrite ?node_44607.
  rewrite ?node_44608.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44610 (s : N.State) (i : N.Inputs) :
  R.v44610 (state s) (inputs i) = Zmod.unsigned (N.v44610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44610 s i)) at 1.
  unfold R.v44610, N.v44610.
  rewrite ?node_44606.
  rewrite ?node_44609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44611 (s : N.State) (i : N.Inputs) :
  R.v44611 (state s) (inputs i) = Zmod.unsigned (N.v44611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44611 s i)) at 1.
  unfold R.v44611, N.v44611.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44612 (s : N.State) (i : N.Inputs) :
  R.v44612 (state s) (inputs i) = Zmod.unsigned (N.v44612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44612 s i)) at 1.
  unfold R.v44612, N.v44612.
  rewrite ?node_12065.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44613 (s : N.State) (i : N.Inputs) :
  R.v44613 (state s) (inputs i) = Zmod.unsigned (N.v44613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44613 s i)) at 1.
  unfold R.v44613, N.v44613.
  rewrite ?node_12061.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44614 (s : N.State) (i : N.Inputs) :
  R.v44614 (state s) (inputs i) = Zmod.unsigned (N.v44614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44614 s i)) at 1.
  unfold R.v44614, N.v44614.
  rewrite ?node_12057.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44615 (s : N.State) (i : N.Inputs) :
  R.v44615 (state s) (inputs i) = Zmod.unsigned (N.v44615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44615 s i)) at 1.
  unfold R.v44615, N.v44615.
  unfold R.v6, N.v6.
  rewrite ?node_12053.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44616 (s : N.State) (i : N.Inputs) :
  R.v44616 (state s) (inputs i) = Zmod.unsigned (N.v44616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44616 s i)) at 1.
  unfold R.v44616, N.v44616.
  unfold R.v6, N.v6.
  rewrite ?node_12050.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44617 (s : N.State) (i : N.Inputs) :
  R.v44617 (state s) (inputs i) = Zmod.unsigned (N.v44617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44617 s i)) at 1.
  unfold R.v44617, N.v44617.
  rewrite ?node_44615.
  rewrite ?node_44616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44618 (s : N.State) (i : N.Inputs) :
  R.v44618 (state s) (inputs i) = Zmod.unsigned (N.v44618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44618 s i)) at 1.
  unfold R.v44618, N.v44618.
  unfold R.v16484, N.v16484.
  rewrite ?node_44617.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44619 (s : N.State) (i : N.Inputs) :
  R.v44619 (state s) (inputs i) = Zmod.unsigned (N.v44619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44619 s i)) at 1.
  unfold R.v44619, N.v44619.
  rewrite ?node_44612.
  rewrite ?node_44613.
  rewrite ?node_44614.
  rewrite ?node_44618.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44620 (s : N.State) (i : N.Inputs) :
  R.v44620 (state s) (inputs i) = Zmod.unsigned (N.v44620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44620 s i)) at 1.
  unfold R.v44620, N.v44620.
  unfold R.v6, N.v6.
  rewrite ?node_44619.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44621 (s : N.State) (i : N.Inputs) :
  R.v44621 (state s) (inputs i) = Zmod.unsigned (N.v44621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44621 s i)) at 1.
  unfold R.v44621, N.v44621.
  rewrite ?node_12066.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44622 (s : N.State) (i : N.Inputs) :
  R.v44622 (state s) (inputs i) = Zmod.unsigned (N.v44622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44622 s i)) at 1.
  unfold R.v44622, N.v44622.
  unfold R.v6, N.v6.
  rewrite ?node_12210.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44623 (s : N.State) (i : N.Inputs) :
  R.v44623 (state s) (inputs i) = Zmod.unsigned (N.v44623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44623 s i)) at 1.
  unfold R.v44623, N.v44623.
  unfold R.v6, N.v6.
  rewrite ?node_12234.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44624 (s : N.State) (i : N.Inputs) :
  R.v44624 (state s) (inputs i) = Zmod.unsigned (N.v44624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44624 s i)) at 1.
  unfold R.v44624, N.v44624.
  rewrite ?node_44621.
  rewrite ?node_44622.
  rewrite ?node_44623.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44625 (s : N.State) (i : N.Inputs) :
  R.v44625 (state s) (inputs i) = Zmod.unsigned (N.v44625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44625 s i)) at 1.
  unfold R.v44625, N.v44625.
  rewrite ?node_44620.
  rewrite ?node_44624.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44626 (s : N.State) (i : N.Inputs) :
  R.v44626 (state s) (inputs i) = Zmod.unsigned (N.v44626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44626 s i)) at 1.
  unfold R.v44626, N.v44626.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44627 (s : N.State) (i : N.Inputs) :
  R.v44627 (state s) (inputs i) = Zmod.unsigned (N.v44627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44627 s i)) at 1.
  unfold R.v44627, N.v44627.
  rewrite ?node_12057.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44628 (s : N.State) (i : N.Inputs) :
  R.v44628 (state s) (inputs i) = Zmod.unsigned (N.v44628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44628 s i)) at 1.
  unfold R.v44628, N.v44628.
  unfold R.v6, N.v6.
  rewrite ?node_12053.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44629 (s : N.State) (i : N.Inputs) :
  R.v44629 (state s) (inputs i) = Zmod.unsigned (N.v44629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44629 s i)) at 1.
  unfold R.v44629, N.v44629.
  unfold R.v6, N.v6.
  rewrite ?node_12050.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44630 (s : N.State) (i : N.Inputs) :
  R.v44630 (state s) (inputs i) = Zmod.unsigned (N.v44630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44630 s i)) at 1.
  unfold R.v44630, N.v44630.
  rewrite ?node_44628.
  rewrite ?node_44629.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44631 (s : N.State) (i : N.Inputs) :
  R.v44631 (state s) (inputs i) = Zmod.unsigned (N.v44631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44631 s i)) at 1.
  unfold R.v44631, N.v44631.
  unfold R.v16484, N.v16484.
  rewrite ?node_44630.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44632 (s : N.State) (i : N.Inputs) :
  R.v44632 (state s) (inputs i) = Zmod.unsigned (N.v44632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44632 s i)) at 1.
  unfold R.v44632, N.v44632.
  rewrite ?node_44627.
  rewrite ?node_44631.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44633 (s : N.State) (i : N.Inputs) :
  R.v44633 (state s) (inputs i) = Zmod.unsigned (N.v44633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44633 s i)) at 1.
  unfold R.v44633, N.v44633.
  unfold R.v6, N.v6.
  rewrite ?node_44632.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44634 (s : N.State) (i : N.Inputs) :
  R.v44634 (state s) (inputs i) = Zmod.unsigned (N.v44634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44634 s i)) at 1.
  unfold R.v44634, N.v44634.
  rewrite ?node_12058.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44635 (s : N.State) (i : N.Inputs) :
  R.v44635 (state s) (inputs i) = Zmod.unsigned (N.v44635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44635 s i)) at 1.
  unfold R.v44635, N.v44635.
  unfold R.v6, N.v6.
  rewrite ?node_12210.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44636 (s : N.State) (i : N.Inputs) :
  R.v44636 (state s) (inputs i) = Zmod.unsigned (N.v44636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44636 s i)) at 1.
  unfold R.v44636, N.v44636.
  rewrite ?node_44634.
  rewrite ?node_44635.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44637 (s : N.State) (i : N.Inputs) :
  R.v44637 (state s) (inputs i) = Zmod.unsigned (N.v44637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44637 s i)) at 1.
  unfold R.v44637, N.v44637.
  rewrite ?node_44633.
  rewrite ?node_44636.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44638 (s : N.State) (i : N.Inputs) :
  R.v44638 (state s) (inputs i) = Zmod.unsigned (N.v44638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44638 s i)) at 1.
  unfold R.v44638, N.v44638.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44639 (s : N.State) (i : N.Inputs) :
  R.v44639 (state s) (inputs i) = Zmod.unsigned (N.v44639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44639 s i)) at 1.
  unfold R.v44639, N.v44639.
  rewrite ?node_12065.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44640 (s : N.State) (i : N.Inputs) :
  R.v44640 (state s) (inputs i) = Zmod.unsigned (N.v44640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44640 s i)) at 1.
  unfold R.v44640, N.v44640.
  unfold R.v6, N.v6.
  rewrite ?node_12061.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44641 (s : N.State) (i : N.Inputs) :
  R.v44641 (state s) (inputs i) = Zmod.unsigned (N.v44641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44641 s i)) at 1.
  unfold R.v44641, N.v44641.
  unfold R.v6, N.v6.
  rewrite ?node_12058.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44642 (s : N.State) (i : N.Inputs) :
  R.v44642 (state s) (inputs i) = Zmod.unsigned (N.v44642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44642 s i)) at 1.
  unfold R.v44642, N.v44642.
  rewrite ?node_44640.
  rewrite ?node_44641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44643 (s : N.State) (i : N.Inputs) :
  R.v44643 (state s) (inputs i) = Zmod.unsigned (N.v44643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44643 s i)) at 1.
  unfold R.v44643, N.v44643.
  unfold R.v16484, N.v16484.
  rewrite ?node_44642.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44644 (s : N.State) (i : N.Inputs) :
  R.v44644 (state s) (inputs i) = Zmod.unsigned (N.v44644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44644 s i)) at 1.
  unfold R.v44644, N.v44644.
  rewrite ?node_44639.
  rewrite ?node_44643.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44645 (s : N.State) (i : N.Inputs) :
  R.v44645 (state s) (inputs i) = Zmod.unsigned (N.v44645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44645 s i)) at 1.
  unfold R.v44645, N.v44645.
  unfold R.v6, N.v6.
  rewrite ?node_44644.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44646 (s : N.State) (i : N.Inputs) :
  R.v44646 (state s) (inputs i) = Zmod.unsigned (N.v44646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44646 s i)) at 1.
  unfold R.v44646, N.v44646.
  rewrite ?node_12066.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44647 (s : N.State) (i : N.Inputs) :
  R.v44647 (state s) (inputs i) = Zmod.unsigned (N.v44647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44647 s i)) at 1.
  unfold R.v44647, N.v44647.
  unfold R.v6, N.v6.
  rewrite ?node_12234.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44648 (s : N.State) (i : N.Inputs) :
  R.v44648 (state s) (inputs i) = Zmod.unsigned (N.v44648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44648 s i)) at 1.
  unfold R.v44648, N.v44648.
  rewrite ?node_44646.
  rewrite ?node_44647.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44649 (s : N.State) (i : N.Inputs) :
  R.v44649 (state s) (inputs i) = Zmod.unsigned (N.v44649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44649 s i)) at 1.
  unfold R.v44649, N.v44649.
  rewrite ?node_44645.
  rewrite ?node_44648.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44650 (s : N.State) (i : N.Inputs) :
  R.v44650 (state s) (inputs i) = Zmod.unsigned (N.v44650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44650 s i)) at 1.
  unfold R.v44650, N.v44650.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44651 (s : N.State) (i : N.Inputs) :
  R.v44651 (state s) (inputs i) = Zmod.unsigned (N.v44651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44651 s i)) at 1.
  unfold R.v44651, N.v44651.
  rewrite ?node_12077.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44652 (s : N.State) (i : N.Inputs) :
  R.v44652 (state s) (inputs i) = Zmod.unsigned (N.v44652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44652 s i)) at 1.
  unfold R.v44652, N.v44652.
  unfold R.v6, N.v6.
  rewrite ?node_12073.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44653 (s : N.State) (i : N.Inputs) :
  R.v44653 (state s) (inputs i) = Zmod.unsigned (N.v44653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44653 s i)) at 1.
  unfold R.v44653, N.v44653.
  unfold R.v6, N.v6.
  rewrite ?node_12070.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44654 (s : N.State) (i : N.Inputs) :
  R.v44654 (state s) (inputs i) = Zmod.unsigned (N.v44654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44654 s i)) at 1.
  unfold R.v44654, N.v44654.
  rewrite ?node_44652.
  rewrite ?node_44653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44655 (s : N.State) (i : N.Inputs) :
  R.v44655 (state s) (inputs i) = Zmod.unsigned (N.v44655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44655 s i)) at 1.
  unfold R.v44655, N.v44655.
  unfold R.v16484, N.v16484.
  rewrite ?node_44654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44656 (s : N.State) (i : N.Inputs) :
  R.v44656 (state s) (inputs i) = Zmod.unsigned (N.v44656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44656 s i)) at 1.
  unfold R.v44656, N.v44656.
  rewrite ?node_44651.
  rewrite ?node_44655.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44657 (s : N.State) (i : N.Inputs) :
  R.v44657 (state s) (inputs i) = Zmod.unsigned (N.v44657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44657 s i)) at 1.
  unfold R.v44657, N.v44657.
  unfold R.v6, N.v6.
  rewrite ?node_44656.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44658 (s : N.State) (i : N.Inputs) :
  R.v44658 (state s) (inputs i) = Zmod.unsigned (N.v44658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44658 s i)) at 1.
  unfold R.v44658, N.v44658.
  rewrite ?node_12078.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44659 (s : N.State) (i : N.Inputs) :
  R.v44659 (state s) (inputs i) = Zmod.unsigned (N.v44659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44659 s i)) at 1.
  unfold R.v44659, N.v44659.
  unfold R.v6, N.v6.
  rewrite ?node_12238.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44660 (s : N.State) (i : N.Inputs) :
  R.v44660 (state s) (inputs i) = Zmod.unsigned (N.v44660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44660 s i)) at 1.
  unfold R.v44660, N.v44660.
  rewrite ?node_44658.
  rewrite ?node_44659.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44661 (s : N.State) (i : N.Inputs) :
  R.v44661 (state s) (inputs i) = Zmod.unsigned (N.v44661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44661 s i)) at 1.
  unfold R.v44661, N.v44661.
  rewrite ?node_44657.
  rewrite ?node_44660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44662 (s : N.State) (i : N.Inputs) :
  R.v44662 (state s) (inputs i) = Zmod.unsigned (N.v44662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44662 s i)) at 1.
  unfold R.v44662, N.v44662.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44663 (s : N.State) (i : N.Inputs) :
  R.v44663 (state s) (inputs i) = Zmod.unsigned (N.v44663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44663 s i)) at 1.
  unfold R.v44663, N.v44663.
  rewrite ?node_12159.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44664 (s : N.State) (i : N.Inputs) :
  R.v44664 (state s) (inputs i) = Zmod.unsigned (N.v44664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44664 s i)) at 1.
  unfold R.v44664, N.v44664.
  rewrite ?node_12155.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44665 (s : N.State) (i : N.Inputs) :
  R.v44665 (state s) (inputs i) = Zmod.unsigned (N.v44665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44665 s i)) at 1.
  unfold R.v44665, N.v44665.
  rewrite ?node_12147.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44666 (s : N.State) (i : N.Inputs) :
  R.v44666 (state s) (inputs i) = Zmod.unsigned (N.v44666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44666 s i)) at 1.
  unfold R.v44666, N.v44666.
  unfold R.v6, N.v6.
  rewrite ?node_12139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44667 (s : N.State) (i : N.Inputs) :
  R.v44667 (state s) (inputs i) = Zmod.unsigned (N.v44667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44667 s i)) at 1.
  unfold R.v44667, N.v44667.
  unfold R.v6, N.v6.
  rewrite ?node_12132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44668 (s : N.State) (i : N.Inputs) :
  R.v44668 (state s) (inputs i) = Zmod.unsigned (N.v44668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44668 s i)) at 1.
  unfold R.v44668, N.v44668.
  rewrite ?node_44666.
  rewrite ?node_44667.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44669 (s : N.State) (i : N.Inputs) :
  R.v44669 (state s) (inputs i) = Zmod.unsigned (N.v44669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44669 s i)) at 1.
  unfold R.v44669, N.v44669.
  unfold R.v16484, N.v16484.
  rewrite ?node_44668.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44670 (s : N.State) (i : N.Inputs) :
  R.v44670 (state s) (inputs i) = Zmod.unsigned (N.v44670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44670 s i)) at 1.
  unfold R.v44670, N.v44670.
  rewrite ?node_44663.
  rewrite ?node_44664.
  rewrite ?node_44665.
  rewrite ?node_44669.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44671 (s : N.State) (i : N.Inputs) :
  R.v44671 (state s) (inputs i) = Zmod.unsigned (N.v44671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44671 s i)) at 1.
  unfold R.v44671, N.v44671.
  unfold R.v6, N.v6.
  rewrite ?node_44670.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44672 (s : N.State) (i : N.Inputs) :
  R.v44672 (state s) (inputs i) = Zmod.unsigned (N.v44672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44672 s i)) at 1.
  unfold R.v44672, N.v44672.
  rewrite ?node_12160.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44673 (s : N.State) (i : N.Inputs) :
  R.v44673 (state s) (inputs i) = Zmod.unsigned (N.v44673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44673 s i)) at 1.
  unfold R.v44673, N.v44673.
  unfold R.v6, N.v6.
  rewrite ?node_12299.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44674 (s : N.State) (i : N.Inputs) :
  R.v44674 (state s) (inputs i) = Zmod.unsigned (N.v44674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44674 s i)) at 1.
  unfold R.v44674, N.v44674.
  unfold R.v6, N.v6.
  rewrite ?node_12367.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44675 (s : N.State) (i : N.Inputs) :
  R.v44675 (state s) (inputs i) = Zmod.unsigned (N.v44675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44675 s i)) at 1.
  unfold R.v44675, N.v44675.
  rewrite ?node_44672.
  rewrite ?node_44673.
  rewrite ?node_44674.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44676 (s : N.State) (i : N.Inputs) :
  R.v44676 (state s) (inputs i) = Zmod.unsigned (N.v44676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44676 s i)) at 1.
  unfold R.v44676, N.v44676.
  rewrite ?node_44671.
  rewrite ?node_44675.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44677 (s : N.State) (i : N.Inputs) :
  R.v44677 (state s) (inputs i) = Zmod.unsigned (N.v44677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44677 s i)) at 1.
  unfold R.v44677, N.v44677.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44678 (s : N.State) (i : N.Inputs) :
  R.v44678 (state s) (inputs i) = Zmod.unsigned (N.v44678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44678 s i)) at 1.
  unfold R.v44678, N.v44678.
  rewrite ?node_12147.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44679 (s : N.State) (i : N.Inputs) :
  R.v44679 (state s) (inputs i) = Zmod.unsigned (N.v44679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44679 s i)) at 1.
  unfold R.v44679, N.v44679.
  unfold R.v6, N.v6.
  rewrite ?node_12139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44680 (s : N.State) (i : N.Inputs) :
  R.v44680 (state s) (inputs i) = Zmod.unsigned (N.v44680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44680 s i)) at 1.
  unfold R.v44680, N.v44680.
  unfold R.v6, N.v6.
  rewrite ?node_12132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44681 (s : N.State) (i : N.Inputs) :
  R.v44681 (state s) (inputs i) = Zmod.unsigned (N.v44681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44681 s i)) at 1.
  unfold R.v44681, N.v44681.
  rewrite ?node_44679.
  rewrite ?node_44680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44682 (s : N.State) (i : N.Inputs) :
  R.v44682 (state s) (inputs i) = Zmod.unsigned (N.v44682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44682 s i)) at 1.
  unfold R.v44682, N.v44682.
  unfold R.v16484, N.v16484.
  rewrite ?node_44681.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44683 (s : N.State) (i : N.Inputs) :
  R.v44683 (state s) (inputs i) = Zmod.unsigned (N.v44683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44683 s i)) at 1.
  unfold R.v44683, N.v44683.
  rewrite ?node_44678.
  rewrite ?node_44682.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44684 (s : N.State) (i : N.Inputs) :
  R.v44684 (state s) (inputs i) = Zmod.unsigned (N.v44684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44684 s i)) at 1.
  unfold R.v44684, N.v44684.
  unfold R.v6, N.v6.
  rewrite ?node_44683.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44685 (s : N.State) (i : N.Inputs) :
  R.v44685 (state s) (inputs i) = Zmod.unsigned (N.v44685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44685 s i)) at 1.
  unfold R.v44685, N.v44685.
  rewrite ?node_12148.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44686 (s : N.State) (i : N.Inputs) :
  R.v44686 (state s) (inputs i) = Zmod.unsigned (N.v44686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44686 s i)) at 1.
  unfold R.v44686, N.v44686.
  unfold R.v6, N.v6.
  rewrite ?node_12299.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44687 (s : N.State) (i : N.Inputs) :
  R.v44687 (state s) (inputs i) = Zmod.unsigned (N.v44687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44687 s i)) at 1.
  unfold R.v44687, N.v44687.
  rewrite ?node_44685.
  rewrite ?node_44686.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44688 (s : N.State) (i : N.Inputs) :
  R.v44688 (state s) (inputs i) = Zmod.unsigned (N.v44688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44688 s i)) at 1.
  unfold R.v44688, N.v44688.
  rewrite ?node_44684.
  rewrite ?node_44687.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44689 (s : N.State) (i : N.Inputs) :
  R.v44689 (state s) (inputs i) = Zmod.unsigned (N.v44689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44689 s i)) at 1.
  unfold R.v44689, N.v44689.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44690 (s : N.State) (i : N.Inputs) :
  R.v44690 (state s) (inputs i) = Zmod.unsigned (N.v44690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44690 s i)) at 1.
  unfold R.v44690, N.v44690.
  rewrite ?node_12159.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44691 (s : N.State) (i : N.Inputs) :
  R.v44691 (state s) (inputs i) = Zmod.unsigned (N.v44691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44691 s i)) at 1.
  unfold R.v44691, N.v44691.
  unfold R.v6, N.v6.
  rewrite ?node_12155.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44692 (s : N.State) (i : N.Inputs) :
  R.v44692 (state s) (inputs i) = Zmod.unsigned (N.v44692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44692 s i)) at 1.
  unfold R.v44692, N.v44692.
  unfold R.v6, N.v6.
  rewrite ?node_12148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44693 (s : N.State) (i : N.Inputs) :
  R.v44693 (state s) (inputs i) = Zmod.unsigned (N.v44693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44693 s i)) at 1.
  unfold R.v44693, N.v44693.
  rewrite ?node_44691.
  rewrite ?node_44692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44694 (s : N.State) (i : N.Inputs) :
  R.v44694 (state s) (inputs i) = Zmod.unsigned (N.v44694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44694 s i)) at 1.
  unfold R.v44694, N.v44694.
  unfold R.v16484, N.v16484.
  rewrite ?node_44693.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44695 (s : N.State) (i : N.Inputs) :
  R.v44695 (state s) (inputs i) = Zmod.unsigned (N.v44695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44695 s i)) at 1.
  unfold R.v44695, N.v44695.
  rewrite ?node_44690.
  rewrite ?node_44694.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44696 (s : N.State) (i : N.Inputs) :
  R.v44696 (state s) (inputs i) = Zmod.unsigned (N.v44696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44696 s i)) at 1.
  unfold R.v44696, N.v44696.
  unfold R.v6, N.v6.
  rewrite ?node_44695.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44697 (s : N.State) (i : N.Inputs) :
  R.v44697 (state s) (inputs i) = Zmod.unsigned (N.v44697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44697 s i)) at 1.
  unfold R.v44697, N.v44697.
  rewrite ?node_12160.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44698 (s : N.State) (i : N.Inputs) :
  R.v44698 (state s) (inputs i) = Zmod.unsigned (N.v44698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44698 s i)) at 1.
  unfold R.v44698, N.v44698.
  unfold R.v6, N.v6.
  rewrite ?node_12367.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44699 (s : N.State) (i : N.Inputs) :
  R.v44699 (state s) (inputs i) = Zmod.unsigned (N.v44699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44699 s i)) at 1.
  unfold R.v44699, N.v44699.
  rewrite ?node_44697.
  rewrite ?node_44698.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44700 (s : N.State) (i : N.Inputs) :
  R.v44700 (state s) (inputs i) = Zmod.unsigned (N.v44700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44700 s i)) at 1.
  unfold R.v44700, N.v44700.
  rewrite ?node_44696.
  rewrite ?node_44699.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44701 (s : N.State) (i : N.Inputs) :
  R.v44701 (state s) (inputs i) = Zmod.unsigned (N.v44701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44701 s i)) at 1.
  unfold R.v44701, N.v44701.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44702 (s : N.State) (i : N.Inputs) :
  R.v44702 (state s) (inputs i) = Zmod.unsigned (N.v44702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44702 s i)) at 1.
  unfold R.v44702, N.v44702.
  rewrite ?node_12190.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44703 (s : N.State) (i : N.Inputs) :
  R.v44703 (state s) (inputs i) = Zmod.unsigned (N.v44703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44703 s i)) at 1.
  unfold R.v44703, N.v44703.
  rewrite ?node_12186.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44704 (s : N.State) (i : N.Inputs) :
  R.v44704 (state s) (inputs i) = Zmod.unsigned (N.v44704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44704 s i)) at 1.
  unfold R.v44704, N.v44704.
  rewrite ?node_12182.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44705 (s : N.State) (i : N.Inputs) :
  R.v44705 (state s) (inputs i) = Zmod.unsigned (N.v44705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44705 s i)) at 1.
  unfold R.v44705, N.v44705.
  unfold R.v6, N.v6.
  rewrite ?node_12174.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44706 (s : N.State) (i : N.Inputs) :
  R.v44706 (state s) (inputs i) = Zmod.unsigned (N.v44706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44706 s i)) at 1.
  unfold R.v44706, N.v44706.
  unfold R.v6, N.v6.
  rewrite ?node_12167.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44707 (s : N.State) (i : N.Inputs) :
  R.v44707 (state s) (inputs i) = Zmod.unsigned (N.v44707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44707 s i)) at 1.
  unfold R.v44707, N.v44707.
  rewrite ?node_44705.
  rewrite ?node_44706.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44708 (s : N.State) (i : N.Inputs) :
  R.v44708 (state s) (inputs i) = Zmod.unsigned (N.v44708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44708 s i)) at 1.
  unfold R.v44708, N.v44708.
  unfold R.v16484, N.v16484.
  rewrite ?node_44707.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44709 (s : N.State) (i : N.Inputs) :
  R.v44709 (state s) (inputs i) = Zmod.unsigned (N.v44709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44709 s i)) at 1.
  unfold R.v44709, N.v44709.
  rewrite ?node_44702.
  rewrite ?node_44703.
  rewrite ?node_44704.
  rewrite ?node_44708.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44710 (s : N.State) (i : N.Inputs) :
  R.v44710 (state s) (inputs i) = Zmod.unsigned (N.v44710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44710 s i)) at 1.
  unfold R.v44710, N.v44710.
  unfold R.v6, N.v6.
  rewrite ?node_44709.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44711 (s : N.State) (i : N.Inputs) :
  R.v44711 (state s) (inputs i) = Zmod.unsigned (N.v44711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44711 s i)) at 1.
  unfold R.v44711, N.v44711.
  rewrite ?node_12191.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44712 (s : N.State) (i : N.Inputs) :
  R.v44712 (state s) (inputs i) = Zmod.unsigned (N.v44712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44712 s i)) at 1.
  unfold R.v44712, N.v44712.
  unfold R.v6, N.v6.
  rewrite ?node_12330.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44713 (s : N.State) (i : N.Inputs) :
  R.v44713 (state s) (inputs i) = Zmod.unsigned (N.v44713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44713 s i)) at 1.
  unfold R.v44713, N.v44713.
  unfold R.v6, N.v6.
  rewrite ?node_12370.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44714 (s : N.State) (i : N.Inputs) :
  R.v44714 (state s) (inputs i) = Zmod.unsigned (N.v44714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44714 s i)) at 1.
  unfold R.v44714, N.v44714.
  rewrite ?node_44711.
  rewrite ?node_44712.
  rewrite ?node_44713.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44715 (s : N.State) (i : N.Inputs) :
  R.v44715 (state s) (inputs i) = Zmod.unsigned (N.v44715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44715 s i)) at 1.
  unfold R.v44715, N.v44715.
  rewrite ?node_44710.
  rewrite ?node_44714.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44716 (s : N.State) (i : N.Inputs) :
  R.v44716 (state s) (inputs i) = Zmod.unsigned (N.v44716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44716 s i)) at 1.
  unfold R.v44716, N.v44716.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44717 (s : N.State) (i : N.Inputs) :
  R.v44717 (state s) (inputs i) = Zmod.unsigned (N.v44717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44717 s i)) at 1.
  unfold R.v44717, N.v44717.
  rewrite ?node_12182.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44718 (s : N.State) (i : N.Inputs) :
  R.v44718 (state s) (inputs i) = Zmod.unsigned (N.v44718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44718 s i)) at 1.
  unfold R.v44718, N.v44718.
  unfold R.v6, N.v6.
  rewrite ?node_12174.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44719 (s : N.State) (i : N.Inputs) :
  R.v44719 (state s) (inputs i) = Zmod.unsigned (N.v44719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44719 s i)) at 1.
  unfold R.v44719, N.v44719.
  unfold R.v6, N.v6.
  rewrite ?node_12167.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44720 (s : N.State) (i : N.Inputs) :
  R.v44720 (state s) (inputs i) = Zmod.unsigned (N.v44720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44720 s i)) at 1.
  unfold R.v44720, N.v44720.
  rewrite ?node_44718.
  rewrite ?node_44719.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44721 (s : N.State) (i : N.Inputs) :
  R.v44721 (state s) (inputs i) = Zmod.unsigned (N.v44721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44721 s i)) at 1.
  unfold R.v44721, N.v44721.
  unfold R.v16484, N.v16484.
  rewrite ?node_44720.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44722 (s : N.State) (i : N.Inputs) :
  R.v44722 (state s) (inputs i) = Zmod.unsigned (N.v44722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44722 s i)) at 1.
  unfold R.v44722, N.v44722.
  rewrite ?node_44717.
  rewrite ?node_44721.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44723 (s : N.State) (i : N.Inputs) :
  R.v44723 (state s) (inputs i) = Zmod.unsigned (N.v44723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44723 s i)) at 1.
  unfold R.v44723, N.v44723.
  unfold R.v6, N.v6.
  rewrite ?node_44722.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44724 (s : N.State) (i : N.Inputs) :
  R.v44724 (state s) (inputs i) = Zmod.unsigned (N.v44724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44724 s i)) at 1.
  unfold R.v44724, N.v44724.
  rewrite ?node_12183.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44725 (s : N.State) (i : N.Inputs) :
  R.v44725 (state s) (inputs i) = Zmod.unsigned (N.v44725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44725 s i)) at 1.
  unfold R.v44725, N.v44725.
  unfold R.v6, N.v6.
  rewrite ?node_12330.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44726 (s : N.State) (i : N.Inputs) :
  R.v44726 (state s) (inputs i) = Zmod.unsigned (N.v44726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44726 s i)) at 1.
  unfold R.v44726, N.v44726.
  rewrite ?node_44724.
  rewrite ?node_44725.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44727 (s : N.State) (i : N.Inputs) :
  R.v44727 (state s) (inputs i) = Zmod.unsigned (N.v44727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44727 s i)) at 1.
  unfold R.v44727, N.v44727.
  rewrite ?node_44723.
  rewrite ?node_44726.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44728 (s : N.State) (i : N.Inputs) :
  R.v44728 (state s) (inputs i) = Zmod.unsigned (N.v44728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44728 s i)) at 1.
  unfold R.v44728, N.v44728.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44729 (s : N.State) (i : N.Inputs) :
  R.v44729 (state s) (inputs i) = Zmod.unsigned (N.v44729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44729 s i)) at 1.
  unfold R.v44729, N.v44729.
  rewrite ?node_12190.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44730 (s : N.State) (i : N.Inputs) :
  R.v44730 (state s) (inputs i) = Zmod.unsigned (N.v44730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44730 s i)) at 1.
  unfold R.v44730, N.v44730.
  unfold R.v6, N.v6.
  rewrite ?node_12186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44731 (s : N.State) (i : N.Inputs) :
  R.v44731 (state s) (inputs i) = Zmod.unsigned (N.v44731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44731 s i)) at 1.
  unfold R.v44731, N.v44731.
  unfold R.v6, N.v6.
  rewrite ?node_12183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44732 (s : N.State) (i : N.Inputs) :
  R.v44732 (state s) (inputs i) = Zmod.unsigned (N.v44732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44732 s i)) at 1.
  unfold R.v44732, N.v44732.
  rewrite ?node_44730.
  rewrite ?node_44731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44733 (s : N.State) (i : N.Inputs) :
  R.v44733 (state s) (inputs i) = Zmod.unsigned (N.v44733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44733 s i)) at 1.
  unfold R.v44733, N.v44733.
  unfold R.v16484, N.v16484.
  rewrite ?node_44732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44734 (s : N.State) (i : N.Inputs) :
  R.v44734 (state s) (inputs i) = Zmod.unsigned (N.v44734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44734 s i)) at 1.
  unfold R.v44734, N.v44734.
  rewrite ?node_44729.
  rewrite ?node_44733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44735 (s : N.State) (i : N.Inputs) :
  R.v44735 (state s) (inputs i) = Zmod.unsigned (N.v44735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44735 s i)) at 1.
  unfold R.v44735, N.v44735.
  unfold R.v6, N.v6.
  rewrite ?node_44734.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44736 (s : N.State) (i : N.Inputs) :
  R.v44736 (state s) (inputs i) = Zmod.unsigned (N.v44736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44736 s i)) at 1.
  unfold R.v44736, N.v44736.
  rewrite ?node_12191.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44737 (s : N.State) (i : N.Inputs) :
  R.v44737 (state s) (inputs i) = Zmod.unsigned (N.v44737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44737 s i)) at 1.
  unfold R.v44737, N.v44737.
  unfold R.v6, N.v6.
  rewrite ?node_12370.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44738 (s : N.State) (i : N.Inputs) :
  R.v44738 (state s) (inputs i) = Zmod.unsigned (N.v44738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44738 s i)) at 1.
  unfold R.v44738, N.v44738.
  rewrite ?node_44736.
  rewrite ?node_44737.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44739 (s : N.State) (i : N.Inputs) :
  R.v44739 (state s) (inputs i) = Zmod.unsigned (N.v44739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44739 s i)) at 1.
  unfold R.v44739, N.v44739.
  rewrite ?node_44735.
  rewrite ?node_44738.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44740 (s : N.State) (i : N.Inputs) :
  R.v44740 (state s) (inputs i) = Zmod.unsigned (N.v44740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44740 s i)) at 1.
  unfold R.v44740, N.v44740.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44741 (s : N.State) (i : N.Inputs) :
  R.v44741 (state s) (inputs i) = Zmod.unsigned (N.v44741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44741 s i)) at 1.
  unfold R.v44741, N.v44741.
  rewrite ?node_12210.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44742 (s : N.State) (i : N.Inputs) :
  R.v44742 (state s) (inputs i) = Zmod.unsigned (N.v44742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44742 s i)) at 1.
  unfold R.v44742, N.v44742.
  rewrite ?node_12206.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44743 (s : N.State) (i : N.Inputs) :
  R.v44743 (state s) (inputs i) = Zmod.unsigned (N.v44743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44743 s i)) at 1.
  unfold R.v44743, N.v44743.
  rewrite ?node_12202.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44744 (s : N.State) (i : N.Inputs) :
  R.v44744 (state s) (inputs i) = Zmod.unsigned (N.v44744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44744 s i)) at 1.
  unfold R.v44744, N.v44744.
  unfold R.v6, N.v6.
  rewrite ?node_12198.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44745 (s : N.State) (i : N.Inputs) :
  R.v44745 (state s) (inputs i) = Zmod.unsigned (N.v44745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44745 s i)) at 1.
  unfold R.v44745, N.v44745.
  unfold R.v6, N.v6.
  rewrite ?node_12195.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44746 (s : N.State) (i : N.Inputs) :
  R.v44746 (state s) (inputs i) = Zmod.unsigned (N.v44746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44746 s i)) at 1.
  unfold R.v44746, N.v44746.
  rewrite ?node_44744.
  rewrite ?node_44745.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44747 (s : N.State) (i : N.Inputs) :
  R.v44747 (state s) (inputs i) = Zmod.unsigned (N.v44747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44747 s i)) at 1.
  unfold R.v44747, N.v44747.
  unfold R.v16484, N.v16484.
  rewrite ?node_44746.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44748 (s : N.State) (i : N.Inputs) :
  R.v44748 (state s) (inputs i) = Zmod.unsigned (N.v44748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44748 s i)) at 1.
  unfold R.v44748, N.v44748.
  rewrite ?node_44741.
  rewrite ?node_44742.
  rewrite ?node_44743.
  rewrite ?node_44747.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44749 (s : N.State) (i : N.Inputs) :
  R.v44749 (state s) (inputs i) = Zmod.unsigned (N.v44749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44749 s i)) at 1.
  unfold R.v44749, N.v44749.
  unfold R.v6, N.v6.
  rewrite ?node_44748.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44750 (s : N.State) (i : N.Inputs) :
  R.v44750 (state s) (inputs i) = Zmod.unsigned (N.v44750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44750 s i)) at 1.
  unfold R.v44750, N.v44750.
  rewrite ?node_12211.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44751 (s : N.State) (i : N.Inputs) :
  R.v44751 (state s) (inputs i) = Zmod.unsigned (N.v44751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44751 s i)) at 1.
  unfold R.v44751, N.v44751.
  unfold R.v6, N.v6.
  rewrite ?node_12350.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44752 (s : N.State) (i : N.Inputs) :
  R.v44752 (state s) (inputs i) = Zmod.unsigned (N.v44752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44752 s i)) at 1.
  unfold R.v44752, N.v44752.
  unfold R.v6, N.v6.
  rewrite ?node_12374.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44753 (s : N.State) (i : N.Inputs) :
  R.v44753 (state s) (inputs i) = Zmod.unsigned (N.v44753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44753 s i)) at 1.
  unfold R.v44753, N.v44753.
  rewrite ?node_44750.
  rewrite ?node_44751.
  rewrite ?node_44752.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44754 (s : N.State) (i : N.Inputs) :
  R.v44754 (state s) (inputs i) = Zmod.unsigned (N.v44754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44754 s i)) at 1.
  unfold R.v44754, N.v44754.
  rewrite ?node_44749.
  rewrite ?node_44753.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44755 (s : N.State) (i : N.Inputs) :
  R.v44755 (state s) (inputs i) = Zmod.unsigned (N.v44755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44755 s i)) at 1.
  unfold R.v44755, N.v44755.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44756 (s : N.State) (i : N.Inputs) :
  R.v44756 (state s) (inputs i) = Zmod.unsigned (N.v44756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44756 s i)) at 1.
  unfold R.v44756, N.v44756.
  rewrite ?node_12202.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44757 (s : N.State) (i : N.Inputs) :
  R.v44757 (state s) (inputs i) = Zmod.unsigned (N.v44757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44757 s i)) at 1.
  unfold R.v44757, N.v44757.
  unfold R.v6, N.v6.
  rewrite ?node_12198.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44758 (s : N.State) (i : N.Inputs) :
  R.v44758 (state s) (inputs i) = Zmod.unsigned (N.v44758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44758 s i)) at 1.
  unfold R.v44758, N.v44758.
  unfold R.v6, N.v6.
  rewrite ?node_12195.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44759 (s : N.State) (i : N.Inputs) :
  R.v44759 (state s) (inputs i) = Zmod.unsigned (N.v44759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44759 s i)) at 1.
  unfold R.v44759, N.v44759.
  rewrite ?node_44757.
  rewrite ?node_44758.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44760 (s : N.State) (i : N.Inputs) :
  R.v44760 (state s) (inputs i) = Zmod.unsigned (N.v44760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44760 s i)) at 1.
  unfold R.v44760, N.v44760.
  unfold R.v16484, N.v16484.
  rewrite ?node_44759.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44761 (s : N.State) (i : N.Inputs) :
  R.v44761 (state s) (inputs i) = Zmod.unsigned (N.v44761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44761 s i)) at 1.
  unfold R.v44761, N.v44761.
  rewrite ?node_44756.
  rewrite ?node_44760.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44762 (s : N.State) (i : N.Inputs) :
  R.v44762 (state s) (inputs i) = Zmod.unsigned (N.v44762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44762 s i)) at 1.
  unfold R.v44762, N.v44762.
  unfold R.v6, N.v6.
  rewrite ?node_44761.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44763 (s : N.State) (i : N.Inputs) :
  R.v44763 (state s) (inputs i) = Zmod.unsigned (N.v44763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44763 s i)) at 1.
  unfold R.v44763, N.v44763.
  rewrite ?node_12203.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44764 (s : N.State) (i : N.Inputs) :
  R.v44764 (state s) (inputs i) = Zmod.unsigned (N.v44764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44764 s i)) at 1.
  unfold R.v44764, N.v44764.
  unfold R.v6, N.v6.
  rewrite ?node_12350.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44765 (s : N.State) (i : N.Inputs) :
  R.v44765 (state s) (inputs i) = Zmod.unsigned (N.v44765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44765 s i)) at 1.
  unfold R.v44765, N.v44765.
  rewrite ?node_44763.
  rewrite ?node_44764.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44766 (s : N.State) (i : N.Inputs) :
  R.v44766 (state s) (inputs i) = Zmod.unsigned (N.v44766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44766 s i)) at 1.
  unfold R.v44766, N.v44766.
  rewrite ?node_44762.
  rewrite ?node_44765.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44767 (s : N.State) (i : N.Inputs) :
  R.v44767 (state s) (inputs i) = Zmod.unsigned (N.v44767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44767 s i)) at 1.
  unfold R.v44767, N.v44767.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44768 (s : N.State) (i : N.Inputs) :
  R.v44768 (state s) (inputs i) = Zmod.unsigned (N.v44768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44768 s i)) at 1.
  unfold R.v44768, N.v44768.
  rewrite ?node_12210.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44769 (s : N.State) (i : N.Inputs) :
  R.v44769 (state s) (inputs i) = Zmod.unsigned (N.v44769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44769 s i)) at 1.
  unfold R.v44769, N.v44769.
  unfold R.v6, N.v6.
  rewrite ?node_12206.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44770 (s : N.State) (i : N.Inputs) :
  R.v44770 (state s) (inputs i) = Zmod.unsigned (N.v44770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44770 s i)) at 1.
  unfold R.v44770, N.v44770.
  unfold R.v6, N.v6.
  rewrite ?node_12203.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44771 (s : N.State) (i : N.Inputs) :
  R.v44771 (state s) (inputs i) = Zmod.unsigned (N.v44771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44771 s i)) at 1.
  unfold R.v44771, N.v44771.
  rewrite ?node_44769.
  rewrite ?node_44770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44772 (s : N.State) (i : N.Inputs) :
  R.v44772 (state s) (inputs i) = Zmod.unsigned (N.v44772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44772 s i)) at 1.
  unfold R.v44772, N.v44772.
  unfold R.v16484, N.v16484.
  rewrite ?node_44771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44773 (s : N.State) (i : N.Inputs) :
  R.v44773 (state s) (inputs i) = Zmod.unsigned (N.v44773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44773 s i)) at 1.
  unfold R.v44773, N.v44773.
  rewrite ?node_44768.
  rewrite ?node_44772.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44774 (s : N.State) (i : N.Inputs) :
  R.v44774 (state s) (inputs i) = Zmod.unsigned (N.v44774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44774 s i)) at 1.
  unfold R.v44774, N.v44774.
  unfold R.v6, N.v6.
  rewrite ?node_44773.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44775 (s : N.State) (i : N.Inputs) :
  R.v44775 (state s) (inputs i) = Zmod.unsigned (N.v44775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44775 s i)) at 1.
  unfold R.v44775, N.v44775.
  rewrite ?node_12211.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44776 (s : N.State) (i : N.Inputs) :
  R.v44776 (state s) (inputs i) = Zmod.unsigned (N.v44776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44776 s i)) at 1.
  unfold R.v44776, N.v44776.
  unfold R.v6, N.v6.
  rewrite ?node_12374.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44777 (s : N.State) (i : N.Inputs) :
  R.v44777 (state s) (inputs i) = Zmod.unsigned (N.v44777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44777 s i)) at 1.
  unfold R.v44777, N.v44777.
  rewrite ?node_44775.
  rewrite ?node_44776.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44778 (s : N.State) (i : N.Inputs) :
  R.v44778 (state s) (inputs i) = Zmod.unsigned (N.v44778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44778 s i)) at 1.
  unfold R.v44778, N.v44778.
  rewrite ?node_44774.
  rewrite ?node_44777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44779 (s : N.State) (i : N.Inputs) :
  R.v44779 (state s) (inputs i) = Zmod.unsigned (N.v44779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44779 s i)) at 1.
  unfold R.v44779, N.v44779.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44780 (s : N.State) (i : N.Inputs) :
  R.v44780 (state s) (inputs i) = Zmod.unsigned (N.v44780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44780 s i)) at 1.
  unfold R.v44780, N.v44780.
  unfold R.v6, N.v6.
  rewrite ?node_12218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44781 (s : N.State) (i : N.Inputs) :
  R.v44781 (state s) (inputs i) = Zmod.unsigned (N.v44781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44781 s i)) at 1.
  unfold R.v44781, N.v44781.
  unfold R.v6, N.v6.
  rewrite ?node_12215.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44782 (s : N.State) (i : N.Inputs) :
  R.v44782 (state s) (inputs i) = Zmod.unsigned (N.v44782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44782 s i)) at 1.
  unfold R.v44782, N.v44782.
  rewrite ?node_44780.
  rewrite ?node_44781.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44783 (s : N.State) (i : N.Inputs) :
  R.v44783 (state s) (inputs i) = Zmod.unsigned (N.v44783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44783 s i)) at 1.
  unfold R.v44783, N.v44783.
  unfold R.v16463, N.v16463.
  rewrite ?node_44782.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44784 (s : N.State) (i : N.Inputs) :
  R.v44784 (state s) (inputs i) = Zmod.unsigned (N.v44784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44784 s i)) at 1.
  unfold R.v44784, N.v44784.
  rewrite ?node_12219.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44785 (s : N.State) (i : N.Inputs) :
  R.v44785 (state s) (inputs i) = Zmod.unsigned (N.v44785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44785 s i)) at 1.
  unfold R.v44785, N.v44785.
  unfold R.v6, N.v6.
  rewrite ?node_12376.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44786 (s : N.State) (i : N.Inputs) :
  R.v44786 (state s) (inputs i) = Zmod.unsigned (N.v44786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44786 s i)) at 1.
  unfold R.v44786, N.v44786.
  rewrite ?node_44784.
  rewrite ?node_44785.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44787 (s : N.State) (i : N.Inputs) :
  R.v44787 (state s) (inputs i) = Zmod.unsigned (N.v44787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44787 s i)) at 1.
  unfold R.v44787, N.v44787.
  rewrite ?node_44783.
  rewrite ?node_44786.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44788 (s : N.State) (i : N.Inputs) :
  R.v44788 (state s) (inputs i) = Zmod.unsigned (N.v44788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44788 s i)) at 1.
  unfold R.v44788, N.v44788.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44789 (s : N.State) (i : N.Inputs) :
  R.v44789 (state s) (inputs i) = Zmod.unsigned (N.v44789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44789 s i)) at 1.
  unfold R.v44789, N.v44789.
  rewrite ?node_12299.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44790 (s : N.State) (i : N.Inputs) :
  R.v44790 (state s) (inputs i) = Zmod.unsigned (N.v44790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44790 s i)) at 1.
  unfold R.v44790, N.v44790.
  rewrite ?node_12295.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44791 (s : N.State) (i : N.Inputs) :
  R.v44791 (state s) (inputs i) = Zmod.unsigned (N.v44791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44791 s i)) at 1.
  unfold R.v44791, N.v44791.
  rewrite ?node_12287.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44792 (s : N.State) (i : N.Inputs) :
  R.v44792 (state s) (inputs i) = Zmod.unsigned (N.v44792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44792 s i)) at 1.
  unfold R.v44792, N.v44792.
  unfold R.v6, N.v6.
  rewrite ?node_12279.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44793 (s : N.State) (i : N.Inputs) :
  R.v44793 (state s) (inputs i) = Zmod.unsigned (N.v44793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44793 s i)) at 1.
  unfold R.v44793, N.v44793.
  unfold R.v6, N.v6.
  rewrite ?node_12272.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44794 (s : N.State) (i : N.Inputs) :
  R.v44794 (state s) (inputs i) = Zmod.unsigned (N.v44794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44794 s i)) at 1.
  unfold R.v44794, N.v44794.
  rewrite ?node_44792.
  rewrite ?node_44793.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44795 (s : N.State) (i : N.Inputs) :
  R.v44795 (state s) (inputs i) = Zmod.unsigned (N.v44795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44795 s i)) at 1.
  unfold R.v44795, N.v44795.
  unfold R.v16484, N.v16484.
  rewrite ?node_44794.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44796 (s : N.State) (i : N.Inputs) :
  R.v44796 (state s) (inputs i) = Zmod.unsigned (N.v44796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44796 s i)) at 1.
  unfold R.v44796, N.v44796.
  rewrite ?node_44789.
  rewrite ?node_44790.
  rewrite ?node_44791.
  rewrite ?node_44795.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44797 (s : N.State) (i : N.Inputs) :
  R.v44797 (state s) (inputs i) = Zmod.unsigned (N.v44797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44797 s i)) at 1.
  unfold R.v44797, N.v44797.
  unfold R.v6, N.v6.
  rewrite ?node_44796.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44798 (s : N.State) (i : N.Inputs) :
  R.v44798 (state s) (inputs i) = Zmod.unsigned (N.v44798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44798 s i)) at 1.
  unfold R.v44798, N.v44798.
  rewrite ?node_12300.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44799 (s : N.State) (i : N.Inputs) :
  R.v44799 (state s) (inputs i) = Zmod.unsigned (N.v44799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44799 s i)) at 1.
  unfold R.v44799, N.v44799.
  unfold R.v6, N.v6.
  rewrite ?node_12434.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44800 (s : N.State) (i : N.Inputs) :
  R.v44800 (state s) (inputs i) = Zmod.unsigned (N.v44800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44800 s i)) at 1.
  unfold R.v44800, N.v44800.
  unfold R.v6, N.v6.
  rewrite ?node_12501.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44801 (s : N.State) (i : N.Inputs) :
  R.v44801 (state s) (inputs i) = Zmod.unsigned (N.v44801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44801 s i)) at 1.
  unfold R.v44801, N.v44801.
  rewrite ?node_44798.
  rewrite ?node_44799.
  rewrite ?node_44800.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44802 (s : N.State) (i : N.Inputs) :
  R.v44802 (state s) (inputs i) = Zmod.unsigned (N.v44802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44802 s i)) at 1.
  unfold R.v44802, N.v44802.
  rewrite ?node_44797.
  rewrite ?node_44801.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44803 (s : N.State) (i : N.Inputs) :
  R.v44803 (state s) (inputs i) = Zmod.unsigned (N.v44803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44803 s i)) at 1.
  unfold R.v44803, N.v44803.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44804 (s : N.State) (i : N.Inputs) :
  R.v44804 (state s) (inputs i) = Zmod.unsigned (N.v44804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44804 s i)) at 1.
  unfold R.v44804, N.v44804.
  rewrite ?node_12287.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44805 (s : N.State) (i : N.Inputs) :
  R.v44805 (state s) (inputs i) = Zmod.unsigned (N.v44805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44805 s i)) at 1.
  unfold R.v44805, N.v44805.
  unfold R.v6, N.v6.
  rewrite ?node_12279.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44806 (s : N.State) (i : N.Inputs) :
  R.v44806 (state s) (inputs i) = Zmod.unsigned (N.v44806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44806 s i)) at 1.
  unfold R.v44806, N.v44806.
  unfold R.v6, N.v6.
  rewrite ?node_12272.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44807 (s : N.State) (i : N.Inputs) :
  R.v44807 (state s) (inputs i) = Zmod.unsigned (N.v44807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44807 s i)) at 1.
  unfold R.v44807, N.v44807.
  rewrite ?node_44805.
  rewrite ?node_44806.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44808 (s : N.State) (i : N.Inputs) :
  R.v44808 (state s) (inputs i) = Zmod.unsigned (N.v44808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44808 s i)) at 1.
  unfold R.v44808, N.v44808.
  unfold R.v16484, N.v16484.
  rewrite ?node_44807.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44809 (s : N.State) (i : N.Inputs) :
  R.v44809 (state s) (inputs i) = Zmod.unsigned (N.v44809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44809 s i)) at 1.
  unfold R.v44809, N.v44809.
  rewrite ?node_44804.
  rewrite ?node_44808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44810 (s : N.State) (i : N.Inputs) :
  R.v44810 (state s) (inputs i) = Zmod.unsigned (N.v44810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44810 s i)) at 1.
  unfold R.v44810, N.v44810.
  unfold R.v6, N.v6.
  rewrite ?node_44809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44811 (s : N.State) (i : N.Inputs) :
  R.v44811 (state s) (inputs i) = Zmod.unsigned (N.v44811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44811 s i)) at 1.
  unfold R.v44811, N.v44811.
  rewrite ?node_12288.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44812 (s : N.State) (i : N.Inputs) :
  R.v44812 (state s) (inputs i) = Zmod.unsigned (N.v44812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44812 s i)) at 1.
  unfold R.v44812, N.v44812.
  unfold R.v6, N.v6.
  rewrite ?node_12434.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44813 (s : N.State) (i : N.Inputs) :
  R.v44813 (state s) (inputs i) = Zmod.unsigned (N.v44813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44813 s i)) at 1.
  unfold R.v44813, N.v44813.
  rewrite ?node_44811.
  rewrite ?node_44812.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44814 (s : N.State) (i : N.Inputs) :
  R.v44814 (state s) (inputs i) = Zmod.unsigned (N.v44814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44814 s i)) at 1.
  unfold R.v44814, N.v44814.
  rewrite ?node_44810.
  rewrite ?node_44813.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44815 (s : N.State) (i : N.Inputs) :
  R.v44815 (state s) (inputs i) = Zmod.unsigned (N.v44815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44815 s i)) at 1.
  unfold R.v44815, N.v44815.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44816 (s : N.State) (i : N.Inputs) :
  R.v44816 (state s) (inputs i) = Zmod.unsigned (N.v44816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44816 s i)) at 1.
  unfold R.v44816, N.v44816.
  rewrite ?node_12299.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44817 (s : N.State) (i : N.Inputs) :
  R.v44817 (state s) (inputs i) = Zmod.unsigned (N.v44817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44817 s i)) at 1.
  unfold R.v44817, N.v44817.
  unfold R.v6, N.v6.
  rewrite ?node_12295.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44818 (s : N.State) (i : N.Inputs) :
  R.v44818 (state s) (inputs i) = Zmod.unsigned (N.v44818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44818 s i)) at 1.
  unfold R.v44818, N.v44818.
  unfold R.v6, N.v6.
  rewrite ?node_12288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44819 (s : N.State) (i : N.Inputs) :
  R.v44819 (state s) (inputs i) = Zmod.unsigned (N.v44819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44819 s i)) at 1.
  unfold R.v44819, N.v44819.
  rewrite ?node_44817.
  rewrite ?node_44818.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44820 (s : N.State) (i : N.Inputs) :
  R.v44820 (state s) (inputs i) = Zmod.unsigned (N.v44820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44820 s i)) at 1.
  unfold R.v44820, N.v44820.
  unfold R.v16484, N.v16484.
  rewrite ?node_44819.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44821 (s : N.State) (i : N.Inputs) :
  R.v44821 (state s) (inputs i) = Zmod.unsigned (N.v44821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44821 s i)) at 1.
  unfold R.v44821, N.v44821.
  rewrite ?node_44816.
  rewrite ?node_44820.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44822 (s : N.State) (i : N.Inputs) :
  R.v44822 (state s) (inputs i) = Zmod.unsigned (N.v44822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44822 s i)) at 1.
  unfold R.v44822, N.v44822.
  unfold R.v6, N.v6.
  rewrite ?node_44821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44823 (s : N.State) (i : N.Inputs) :
  R.v44823 (state s) (inputs i) = Zmod.unsigned (N.v44823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44823 s i)) at 1.
  unfold R.v44823, N.v44823.
  rewrite ?node_12300.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44824 (s : N.State) (i : N.Inputs) :
  R.v44824 (state s) (inputs i) = Zmod.unsigned (N.v44824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44824 s i)) at 1.
  unfold R.v44824, N.v44824.
  unfold R.v6, N.v6.
  rewrite ?node_12501.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44825 (s : N.State) (i : N.Inputs) :
  R.v44825 (state s) (inputs i) = Zmod.unsigned (N.v44825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44825 s i)) at 1.
  unfold R.v44825, N.v44825.
  rewrite ?node_44823.
  rewrite ?node_44824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44826 (s : N.State) (i : N.Inputs) :
  R.v44826 (state s) (inputs i) = Zmod.unsigned (N.v44826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44826 s i)) at 1.
  unfold R.v44826, N.v44826.
  rewrite ?node_44822.
  rewrite ?node_44825.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44827 (s : N.State) (i : N.Inputs) :
  R.v44827 (state s) (inputs i) = Zmod.unsigned (N.v44827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44827 s i)) at 1.
  unfold R.v44827, N.v44827.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44828 (s : N.State) (i : N.Inputs) :
  R.v44828 (state s) (inputs i) = Zmod.unsigned (N.v44828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44828 s i)) at 1.
  unfold R.v44828, N.v44828.
  rewrite ?node_12330.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44829 (s : N.State) (i : N.Inputs) :
  R.v44829 (state s) (inputs i) = Zmod.unsigned (N.v44829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44829 s i)) at 1.
  unfold R.v44829, N.v44829.
  rewrite ?node_12326.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44830 (s : N.State) (i : N.Inputs) :
  R.v44830 (state s) (inputs i) = Zmod.unsigned (N.v44830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44830 s i)) at 1.
  unfold R.v44830, N.v44830.
  rewrite ?node_12322.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44831 (s : N.State) (i : N.Inputs) :
  R.v44831 (state s) (inputs i) = Zmod.unsigned (N.v44831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44831 s i)) at 1.
  unfold R.v44831, N.v44831.
  unfold R.v6, N.v6.
  rewrite ?node_12314.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44832 (s : N.State) (i : N.Inputs) :
  R.v44832 (state s) (inputs i) = Zmod.unsigned (N.v44832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44832 s i)) at 1.
  unfold R.v44832, N.v44832.
  unfold R.v6, N.v6.
  rewrite ?node_12307.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44833 (s : N.State) (i : N.Inputs) :
  R.v44833 (state s) (inputs i) = Zmod.unsigned (N.v44833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44833 s i)) at 1.
  unfold R.v44833, N.v44833.
  rewrite ?node_44831.
  rewrite ?node_44832.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44834 (s : N.State) (i : N.Inputs) :
  R.v44834 (state s) (inputs i) = Zmod.unsigned (N.v44834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44834 s i)) at 1.
  unfold R.v44834, N.v44834.
  unfold R.v16484, N.v16484.
  rewrite ?node_44833.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44835 (s : N.State) (i : N.Inputs) :
  R.v44835 (state s) (inputs i) = Zmod.unsigned (N.v44835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44835 s i)) at 1.
  unfold R.v44835, N.v44835.
  rewrite ?node_44828.
  rewrite ?node_44829.
  rewrite ?node_44830.
  rewrite ?node_44834.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44836 (s : N.State) (i : N.Inputs) :
  R.v44836 (state s) (inputs i) = Zmod.unsigned (N.v44836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44836 s i)) at 1.
  unfold R.v44836, N.v44836.
  unfold R.v6, N.v6.
  rewrite ?node_44835.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44837 (s : N.State) (i : N.Inputs) :
  R.v44837 (state s) (inputs i) = Zmod.unsigned (N.v44837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44837 s i)) at 1.
  unfold R.v44837, N.v44837.
  rewrite ?node_12331.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44838 (s : N.State) (i : N.Inputs) :
  R.v44838 (state s) (inputs i) = Zmod.unsigned (N.v44838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44838 s i)) at 1.
  unfold R.v44838, N.v44838.
  unfold R.v6, N.v6.
  rewrite ?node_12460.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44839 (s : N.State) (i : N.Inputs) :
  R.v44839 (state s) (inputs i) = Zmod.unsigned (N.v44839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44839 s i)) at 1.
  unfold R.v44839, N.v44839.
  unfold R.v6, N.v6.
  rewrite ?node_12504.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44840 (s : N.State) (i : N.Inputs) :
  R.v44840 (state s) (inputs i) = Zmod.unsigned (N.v44840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44840 s i)) at 1.
  unfold R.v44840, N.v44840.
  rewrite ?node_44837.
  rewrite ?node_44838.
  rewrite ?node_44839.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44841 (s : N.State) (i : N.Inputs) :
  R.v44841 (state s) (inputs i) = Zmod.unsigned (N.v44841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44841 s i)) at 1.
  unfold R.v44841, N.v44841.
  rewrite ?node_44836.
  rewrite ?node_44840.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44842 (s : N.State) (i : N.Inputs) :
  R.v44842 (state s) (inputs i) = Zmod.unsigned (N.v44842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44842 s i)) at 1.
  unfold R.v44842, N.v44842.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44843 (s : N.State) (i : N.Inputs) :
  R.v44843 (state s) (inputs i) = Zmod.unsigned (N.v44843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44843 s i)) at 1.
  unfold R.v44843, N.v44843.
  rewrite ?node_12322.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44844 (s : N.State) (i : N.Inputs) :
  R.v44844 (state s) (inputs i) = Zmod.unsigned (N.v44844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44844 s i)) at 1.
  unfold R.v44844, N.v44844.
  unfold R.v6, N.v6.
  rewrite ?node_12314.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44845 (s : N.State) (i : N.Inputs) :
  R.v44845 (state s) (inputs i) = Zmod.unsigned (N.v44845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44845 s i)) at 1.
  unfold R.v44845, N.v44845.
  unfold R.v6, N.v6.
  rewrite ?node_12307.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44846 (s : N.State) (i : N.Inputs) :
  R.v44846 (state s) (inputs i) = Zmod.unsigned (N.v44846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44846 s i)) at 1.
  unfold R.v44846, N.v44846.
  rewrite ?node_44844.
  rewrite ?node_44845.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44847 (s : N.State) (i : N.Inputs) :
  R.v44847 (state s) (inputs i) = Zmod.unsigned (N.v44847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44847 s i)) at 1.
  unfold R.v44847, N.v44847.
  unfold R.v16484, N.v16484.
  rewrite ?node_44846.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44848 (s : N.State) (i : N.Inputs) :
  R.v44848 (state s) (inputs i) = Zmod.unsigned (N.v44848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44848 s i)) at 1.
  unfold R.v44848, N.v44848.
  rewrite ?node_44843.
  rewrite ?node_44847.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44849 (s : N.State) (i : N.Inputs) :
  R.v44849 (state s) (inputs i) = Zmod.unsigned (N.v44849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44849 s i)) at 1.
  unfold R.v44849, N.v44849.
  unfold R.v6, N.v6.
  rewrite ?node_44848.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44850 (s : N.State) (i : N.Inputs) :
  R.v44850 (state s) (inputs i) = Zmod.unsigned (N.v44850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44850 s i)) at 1.
  unfold R.v44850, N.v44850.
  rewrite ?node_12323.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44851 (s : N.State) (i : N.Inputs) :
  R.v44851 (state s) (inputs i) = Zmod.unsigned (N.v44851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44851 s i)) at 1.
  unfold R.v44851, N.v44851.
  unfold R.v6, N.v6.
  rewrite ?node_12460.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44852 (s : N.State) (i : N.Inputs) :
  R.v44852 (state s) (inputs i) = Zmod.unsigned (N.v44852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44852 s i)) at 1.
  unfold R.v44852, N.v44852.
  rewrite ?node_44850.
  rewrite ?node_44851.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44853 (s : N.State) (i : N.Inputs) :
  R.v44853 (state s) (inputs i) = Zmod.unsigned (N.v44853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44853 s i)) at 1.
  unfold R.v44853, N.v44853.
  rewrite ?node_44849.
  rewrite ?node_44852.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44854 (s : N.State) (i : N.Inputs) :
  R.v44854 (state s) (inputs i) = Zmod.unsigned (N.v44854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44854 s i)) at 1.
  unfold R.v44854, N.v44854.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44855 (s : N.State) (i : N.Inputs) :
  R.v44855 (state s) (inputs i) = Zmod.unsigned (N.v44855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44855 s i)) at 1.
  unfold R.v44855, N.v44855.
  rewrite ?node_12330.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44856 (s : N.State) (i : N.Inputs) :
  R.v44856 (state s) (inputs i) = Zmod.unsigned (N.v44856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44856 s i)) at 1.
  unfold R.v44856, N.v44856.
  unfold R.v6, N.v6.
  rewrite ?node_12326.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44857 (s : N.State) (i : N.Inputs) :
  R.v44857 (state s) (inputs i) = Zmod.unsigned (N.v44857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44857 s i)) at 1.
  unfold R.v44857, N.v44857.
  unfold R.v6, N.v6.
  rewrite ?node_12323.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44858 (s : N.State) (i : N.Inputs) :
  R.v44858 (state s) (inputs i) = Zmod.unsigned (N.v44858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44858 s i)) at 1.
  unfold R.v44858, N.v44858.
  rewrite ?node_44856.
  rewrite ?node_44857.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44859 (s : N.State) (i : N.Inputs) :
  R.v44859 (state s) (inputs i) = Zmod.unsigned (N.v44859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44859 s i)) at 1.
  unfold R.v44859, N.v44859.
  unfold R.v16484, N.v16484.
  rewrite ?node_44858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44860 (s : N.State) (i : N.Inputs) :
  R.v44860 (state s) (inputs i) = Zmod.unsigned (N.v44860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44860 s i)) at 1.
  unfold R.v44860, N.v44860.
  rewrite ?node_44855.
  rewrite ?node_44859.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44861 (s : N.State) (i : N.Inputs) :
  R.v44861 (state s) (inputs i) = Zmod.unsigned (N.v44861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44861 s i)) at 1.
  unfold R.v44861, N.v44861.
  unfold R.v6, N.v6.
  rewrite ?node_44860.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44862 (s : N.State) (i : N.Inputs) :
  R.v44862 (state s) (inputs i) = Zmod.unsigned (N.v44862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44862 s i)) at 1.
  unfold R.v44862, N.v44862.
  rewrite ?node_12331.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44863 (s : N.State) (i : N.Inputs) :
  R.v44863 (state s) (inputs i) = Zmod.unsigned (N.v44863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44863 s i)) at 1.
  unfold R.v44863, N.v44863.
  unfold R.v6, N.v6.
  rewrite ?node_12504.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44864 (s : N.State) (i : N.Inputs) :
  R.v44864 (state s) (inputs i) = Zmod.unsigned (N.v44864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44864 s i)) at 1.
  unfold R.v44864, N.v44864.
  rewrite ?node_44862.
  rewrite ?node_44863.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44865 (s : N.State) (i : N.Inputs) :
  R.v44865 (state s) (inputs i) = Zmod.unsigned (N.v44865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44865 s i)) at 1.
  unfold R.v44865, N.v44865.
  rewrite ?node_44861.
  rewrite ?node_44864.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44866 (s : N.State) (i : N.Inputs) :
  R.v44866 (state s) (inputs i) = Zmod.unsigned (N.v44866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44866 s i)) at 1.
  unfold R.v44866, N.v44866.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44867 (s : N.State) (i : N.Inputs) :
  R.v44867 (state s) (inputs i) = Zmod.unsigned (N.v44867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44867 s i)) at 1.
  unfold R.v44867, N.v44867.
  rewrite ?node_12350.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44868 (s : N.State) (i : N.Inputs) :
  R.v44868 (state s) (inputs i) = Zmod.unsigned (N.v44868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44868 s i)) at 1.
  unfold R.v44868, N.v44868.
  rewrite ?node_12346.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44869 (s : N.State) (i : N.Inputs) :
  R.v44869 (state s) (inputs i) = Zmod.unsigned (N.v44869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44869 s i)) at 1.
  unfold R.v44869, N.v44869.
  rewrite ?node_12342.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44870 (s : N.State) (i : N.Inputs) :
  R.v44870 (state s) (inputs i) = Zmod.unsigned (N.v44870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44870 s i)) at 1.
  unfold R.v44870, N.v44870.
  unfold R.v6, N.v6.
  rewrite ?node_12338.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44871 (s : N.State) (i : N.Inputs) :
  R.v44871 (state s) (inputs i) = Zmod.unsigned (N.v44871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44871 s i)) at 1.
  unfold R.v44871, N.v44871.
  unfold R.v6, N.v6.
  rewrite ?node_12335.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44872 (s : N.State) (i : N.Inputs) :
  R.v44872 (state s) (inputs i) = Zmod.unsigned (N.v44872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44872 s i)) at 1.
  unfold R.v44872, N.v44872.
  rewrite ?node_44870.
  rewrite ?node_44871.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44873 (s : N.State) (i : N.Inputs) :
  R.v44873 (state s) (inputs i) = Zmod.unsigned (N.v44873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44873 s i)) at 1.
  unfold R.v44873, N.v44873.
  unfold R.v16484, N.v16484.
  rewrite ?node_44872.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44874 (s : N.State) (i : N.Inputs) :
  R.v44874 (state s) (inputs i) = Zmod.unsigned (N.v44874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44874 s i)) at 1.
  unfold R.v44874, N.v44874.
  rewrite ?node_44867.
  rewrite ?node_44868.
  rewrite ?node_44869.
  rewrite ?node_44873.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44875 (s : N.State) (i : N.Inputs) :
  R.v44875 (state s) (inputs i) = Zmod.unsigned (N.v44875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44875 s i)) at 1.
  unfold R.v44875, N.v44875.
  unfold R.v6, N.v6.
  rewrite ?node_44874.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44876 (s : N.State) (i : N.Inputs) :
  R.v44876 (state s) (inputs i) = Zmod.unsigned (N.v44876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44876 s i)) at 1.
  unfold R.v44876, N.v44876.
  rewrite ?node_12351.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44877 (s : N.State) (i : N.Inputs) :
  R.v44877 (state s) (inputs i) = Zmod.unsigned (N.v44877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44877 s i)) at 1.
  unfold R.v44877, N.v44877.
  unfold R.v6, N.v6.
  rewrite ?node_12480.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44878 (s : N.State) (i : N.Inputs) :
  R.v44878 (state s) (inputs i) = Zmod.unsigned (N.v44878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44878 s i)) at 1.
  unfold R.v44878, N.v44878.
  unfold R.v6, N.v6.
  rewrite ?node_12508.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44879 (s : N.State) (i : N.Inputs) :
  R.v44879 (state s) (inputs i) = Zmod.unsigned (N.v44879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44879 s i)) at 1.
  unfold R.v44879, N.v44879.
  rewrite ?node_44876.
  rewrite ?node_44877.
  rewrite ?node_44878.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44880 (s : N.State) (i : N.Inputs) :
  R.v44880 (state s) (inputs i) = Zmod.unsigned (N.v44880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44880 s i)) at 1.
  unfold R.v44880, N.v44880.
  rewrite ?node_44875.
  rewrite ?node_44879.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44881 (s : N.State) (i : N.Inputs) :
  R.v44881 (state s) (inputs i) = Zmod.unsigned (N.v44881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44881 s i)) at 1.
  unfold R.v44881, N.v44881.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44882 (s : N.State) (i : N.Inputs) :
  R.v44882 (state s) (inputs i) = Zmod.unsigned (N.v44882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44882 s i)) at 1.
  unfold R.v44882, N.v44882.
  rewrite ?node_12342.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44883 (s : N.State) (i : N.Inputs) :
  R.v44883 (state s) (inputs i) = Zmod.unsigned (N.v44883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44883 s i)) at 1.
  unfold R.v44883, N.v44883.
  unfold R.v6, N.v6.
  rewrite ?node_12338.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44884 (s : N.State) (i : N.Inputs) :
  R.v44884 (state s) (inputs i) = Zmod.unsigned (N.v44884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44884 s i)) at 1.
  unfold R.v44884, N.v44884.
  unfold R.v6, N.v6.
  rewrite ?node_12335.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44885 (s : N.State) (i : N.Inputs) :
  R.v44885 (state s) (inputs i) = Zmod.unsigned (N.v44885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44885 s i)) at 1.
  unfold R.v44885, N.v44885.
  rewrite ?node_44883.
  rewrite ?node_44884.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44886 (s : N.State) (i : N.Inputs) :
  R.v44886 (state s) (inputs i) = Zmod.unsigned (N.v44886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44886 s i)) at 1.
  unfold R.v44886, N.v44886.
  unfold R.v16484, N.v16484.
  rewrite ?node_44885.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44887 (s : N.State) (i : N.Inputs) :
  R.v44887 (state s) (inputs i) = Zmod.unsigned (N.v44887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44887 s i)) at 1.
  unfold R.v44887, N.v44887.
  rewrite ?node_44882.
  rewrite ?node_44886.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44888 (s : N.State) (i : N.Inputs) :
  R.v44888 (state s) (inputs i) = Zmod.unsigned (N.v44888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44888 s i)) at 1.
  unfold R.v44888, N.v44888.
  unfold R.v6, N.v6.
  rewrite ?node_44887.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44889 (s : N.State) (i : N.Inputs) :
  R.v44889 (state s) (inputs i) = Zmod.unsigned (N.v44889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44889 s i)) at 1.
  unfold R.v44889, N.v44889.
  rewrite ?node_12343.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44890 (s : N.State) (i : N.Inputs) :
  R.v44890 (state s) (inputs i) = Zmod.unsigned (N.v44890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44890 s i)) at 1.
  unfold R.v44890, N.v44890.
  unfold R.v6, N.v6.
  rewrite ?node_12480.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44891 (s : N.State) (i : N.Inputs) :
  R.v44891 (state s) (inputs i) = Zmod.unsigned (N.v44891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44891 s i)) at 1.
  unfold R.v44891, N.v44891.
  rewrite ?node_44889.
  rewrite ?node_44890.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44892 (s : N.State) (i : N.Inputs) :
  R.v44892 (state s) (inputs i) = Zmod.unsigned (N.v44892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44892 s i)) at 1.
  unfold R.v44892, N.v44892.
  rewrite ?node_44888.
  rewrite ?node_44891.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44893 (s : N.State) (i : N.Inputs) :
  R.v44893 (state s) (inputs i) = Zmod.unsigned (N.v44893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44893 s i)) at 1.
  unfold R.v44893, N.v44893.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44894 (s : N.State) (i : N.Inputs) :
  R.v44894 (state s) (inputs i) = Zmod.unsigned (N.v44894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44894 s i)) at 1.
  unfold R.v44894, N.v44894.
  rewrite ?node_12350.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44895 (s : N.State) (i : N.Inputs) :
  R.v44895 (state s) (inputs i) = Zmod.unsigned (N.v44895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44895 s i)) at 1.
  unfold R.v44895, N.v44895.
  unfold R.v6, N.v6.
  rewrite ?node_12346.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44896 (s : N.State) (i : N.Inputs) :
  R.v44896 (state s) (inputs i) = Zmod.unsigned (N.v44896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44896 s i)) at 1.
  unfold R.v44896, N.v44896.
  unfold R.v6, N.v6.
  rewrite ?node_12343.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44897 (s : N.State) (i : N.Inputs) :
  R.v44897 (state s) (inputs i) = Zmod.unsigned (N.v44897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44897 s i)) at 1.
  unfold R.v44897, N.v44897.
  rewrite ?node_44895.
  rewrite ?node_44896.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44898 (s : N.State) (i : N.Inputs) :
  R.v44898 (state s) (inputs i) = Zmod.unsigned (N.v44898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44898 s i)) at 1.
  unfold R.v44898, N.v44898.
  unfold R.v16484, N.v16484.
  rewrite ?node_44897.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44899 (s : N.State) (i : N.Inputs) :
  R.v44899 (state s) (inputs i) = Zmod.unsigned (N.v44899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44899 s i)) at 1.
  unfold R.v44899, N.v44899.
  rewrite ?node_44894.
  rewrite ?node_44898.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44900 (s : N.State) (i : N.Inputs) :
  R.v44900 (state s) (inputs i) = Zmod.unsigned (N.v44900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44900 s i)) at 1.
  unfold R.v44900, N.v44900.
  unfold R.v6, N.v6.
  rewrite ?node_44899.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44901 (s : N.State) (i : N.Inputs) :
  R.v44901 (state s) (inputs i) = Zmod.unsigned (N.v44901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44901 s i)) at 1.
  unfold R.v44901, N.v44901.
  rewrite ?node_12351.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44902 (s : N.State) (i : N.Inputs) :
  R.v44902 (state s) (inputs i) = Zmod.unsigned (N.v44902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44902 s i)) at 1.
  unfold R.v44902, N.v44902.
  unfold R.v6, N.v6.
  rewrite ?node_12508.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44903 (s : N.State) (i : N.Inputs) :
  R.v44903 (state s) (inputs i) = Zmod.unsigned (N.v44903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44903 s i)) at 1.
  unfold R.v44903, N.v44903.
  rewrite ?node_44901.
  rewrite ?node_44902.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44904 (s : N.State) (i : N.Inputs) :
  R.v44904 (state s) (inputs i) = Zmod.unsigned (N.v44904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44904 s i)) at 1.
  unfold R.v44904, N.v44904.
  rewrite ?node_44900.
  rewrite ?node_44903.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44905 (s : N.State) (i : N.Inputs) :
  R.v44905 (state s) (inputs i) = Zmod.unsigned (N.v44905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44905 s i)) at 1.
  unfold R.v44905, N.v44905.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44906 (s : N.State) (i : N.Inputs) :
  R.v44906 (state s) (inputs i) = Zmod.unsigned (N.v44906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44906 s i)) at 1.
  unfold R.v44906, N.v44906.
  unfold R.v6, N.v6.
  rewrite ?node_12358.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44907 (s : N.State) (i : N.Inputs) :
  R.v44907 (state s) (inputs i) = Zmod.unsigned (N.v44907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44907 s i)) at 1.
  unfold R.v44907, N.v44907.
  unfold R.v6, N.v6.
  rewrite ?node_12355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44908 (s : N.State) (i : N.Inputs) :
  R.v44908 (state s) (inputs i) = Zmod.unsigned (N.v44908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44908 s i)) at 1.
  unfold R.v44908, N.v44908.
  rewrite ?node_44906.
  rewrite ?node_44907.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44909 (s : N.State) (i : N.Inputs) :
  R.v44909 (state s) (inputs i) = Zmod.unsigned (N.v44909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44909 s i)) at 1.
  unfold R.v44909, N.v44909.
  unfold R.v16463, N.v16463.
  rewrite ?node_44908.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44910 (s : N.State) (i : N.Inputs) :
  R.v44910 (state s) (inputs i) = Zmod.unsigned (N.v44910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44910 s i)) at 1.
  unfold R.v44910, N.v44910.
  rewrite ?node_12359.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44911 (s : N.State) (i : N.Inputs) :
  R.v44911 (state s) (inputs i) = Zmod.unsigned (N.v44911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44911 s i)) at 1.
  unfold R.v44911, N.v44911.
  unfold R.v6, N.v6.
  rewrite ?node_12510.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44912 (s : N.State) (i : N.Inputs) :
  R.v44912 (state s) (inputs i) = Zmod.unsigned (N.v44912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44912 s i)) at 1.
  unfold R.v44912, N.v44912.
  rewrite ?node_44910.
  rewrite ?node_44911.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44913 (s : N.State) (i : N.Inputs) :
  R.v44913 (state s) (inputs i) = Zmod.unsigned (N.v44913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44913 s i)) at 1.
  unfold R.v44913, N.v44913.
  rewrite ?node_44909.
  rewrite ?node_44912.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44914 (s : N.State) (i : N.Inputs) :
  R.v44914 (state s) (inputs i) = Zmod.unsigned (N.v44914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44914 s i)) at 1.
  unfold R.v44914, N.v44914.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44915 (s : N.State) (i : N.Inputs) :
  R.v44915 (state s) (inputs i) = Zmod.unsigned (N.v44915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44915 s i)) at 1.
  unfold R.v44915, N.v44915.
  rewrite ?node_12434.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44916 (s : N.State) (i : N.Inputs) :
  R.v44916 (state s) (inputs i) = Zmod.unsigned (N.v44916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44916 s i)) at 1.
  unfold R.v44916, N.v44916.
  rewrite ?node_12430.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44917 (s : N.State) (i : N.Inputs) :
  R.v44917 (state s) (inputs i) = Zmod.unsigned (N.v44917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44917 s i)) at 1.
  unfold R.v44917, N.v44917.
  rewrite ?node_12422.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44918 (s : N.State) (i : N.Inputs) :
  R.v44918 (state s) (inputs i) = Zmod.unsigned (N.v44918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44918 s i)) at 1.
  unfold R.v44918, N.v44918.
  unfold R.v6, N.v6.
  rewrite ?node_12414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44919 (s : N.State) (i : N.Inputs) :
  R.v44919 (state s) (inputs i) = Zmod.unsigned (N.v44919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44919 s i)) at 1.
  unfold R.v44919, N.v44919.
  unfold R.v6, N.v6.
  rewrite ?node_12407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44920 (s : N.State) (i : N.Inputs) :
  R.v44920 (state s) (inputs i) = Zmod.unsigned (N.v44920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44920 s i)) at 1.
  unfold R.v44920, N.v44920.
  rewrite ?node_44918.
  rewrite ?node_44919.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44921 (s : N.State) (i : N.Inputs) :
  R.v44921 (state s) (inputs i) = Zmod.unsigned (N.v44921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44921 s i)) at 1.
  unfold R.v44921, N.v44921.
  unfold R.v16484, N.v16484.
  rewrite ?node_44920.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44922 (s : N.State) (i : N.Inputs) :
  R.v44922 (state s) (inputs i) = Zmod.unsigned (N.v44922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44922 s i)) at 1.
  unfold R.v44922, N.v44922.
  rewrite ?node_44915.
  rewrite ?node_44916.
  rewrite ?node_44917.
  rewrite ?node_44921.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44923 (s : N.State) (i : N.Inputs) :
  R.v44923 (state s) (inputs i) = Zmod.unsigned (N.v44923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44923 s i)) at 1.
  unfold R.v44923, N.v44923.
  unfold R.v6, N.v6.
  rewrite ?node_44922.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44924 (s : N.State) (i : N.Inputs) :
  R.v44924 (state s) (inputs i) = Zmod.unsigned (N.v44924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44924 s i)) at 1.
  unfold R.v44924, N.v44924.
  rewrite ?node_12435.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44925 (s : N.State) (i : N.Inputs) :
  R.v44925 (state s) (inputs i) = Zmod.unsigned (N.v44925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44925 s i)) at 1.
  unfold R.v44925, N.v44925.
  unfold R.v6, N.v6.
  rewrite ?node_12569.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44926 (s : N.State) (i : N.Inputs) :
  R.v44926 (state s) (inputs i) = Zmod.unsigned (N.v44926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44926 s i)) at 1.
  unfold R.v44926, N.v44926.
  unfold R.v6, N.v6.
  rewrite ?node_12632.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44927 (s : N.State) (i : N.Inputs) :
  R.v44927 (state s) (inputs i) = Zmod.unsigned (N.v44927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44927 s i)) at 1.
  unfold R.v44927, N.v44927.
  rewrite ?node_44924.
  rewrite ?node_44925.
  rewrite ?node_44926.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44928 (s : N.State) (i : N.Inputs) :
  R.v44928 (state s) (inputs i) = Zmod.unsigned (N.v44928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44928 s i)) at 1.
  unfold R.v44928, N.v44928.
  rewrite ?node_44923.
  rewrite ?node_44927.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44929 (s : N.State) (i : N.Inputs) :
  R.v44929 (state s) (inputs i) = Zmod.unsigned (N.v44929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44929 s i)) at 1.
  unfold R.v44929, N.v44929.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44930 (s : N.State) (i : N.Inputs) :
  R.v44930 (state s) (inputs i) = Zmod.unsigned (N.v44930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44930 s i)) at 1.
  unfold R.v44930, N.v44930.
  rewrite ?node_12422.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44931 (s : N.State) (i : N.Inputs) :
  R.v44931 (state s) (inputs i) = Zmod.unsigned (N.v44931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44931 s i)) at 1.
  unfold R.v44931, N.v44931.
  unfold R.v6, N.v6.
  rewrite ?node_12414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44932 (s : N.State) (i : N.Inputs) :
  R.v44932 (state s) (inputs i) = Zmod.unsigned (N.v44932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44932 s i)) at 1.
  unfold R.v44932, N.v44932.
  unfold R.v6, N.v6.
  rewrite ?node_12407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44933 (s : N.State) (i : N.Inputs) :
  R.v44933 (state s) (inputs i) = Zmod.unsigned (N.v44933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44933 s i)) at 1.
  unfold R.v44933, N.v44933.
  rewrite ?node_44931.
  rewrite ?node_44932.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44934 (s : N.State) (i : N.Inputs) :
  R.v44934 (state s) (inputs i) = Zmod.unsigned (N.v44934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44934 s i)) at 1.
  unfold R.v44934, N.v44934.
  unfold R.v16484, N.v16484.
  rewrite ?node_44933.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44935 (s : N.State) (i : N.Inputs) :
  R.v44935 (state s) (inputs i) = Zmod.unsigned (N.v44935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44935 s i)) at 1.
  unfold R.v44935, N.v44935.
  rewrite ?node_44930.
  rewrite ?node_44934.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44936 (s : N.State) (i : N.Inputs) :
  R.v44936 (state s) (inputs i) = Zmod.unsigned (N.v44936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44936 s i)) at 1.
  unfold R.v44936, N.v44936.
  unfold R.v6, N.v6.
  rewrite ?node_44935.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44937 (s : N.State) (i : N.Inputs) :
  R.v44937 (state s) (inputs i) = Zmod.unsigned (N.v44937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44937 s i)) at 1.
  unfold R.v44937, N.v44937.
  rewrite ?node_12423.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44938 (s : N.State) (i : N.Inputs) :
  R.v44938 (state s) (inputs i) = Zmod.unsigned (N.v44938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44938 s i)) at 1.
  unfold R.v44938, N.v44938.
  unfold R.v6, N.v6.
  rewrite ?node_12569.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44939 (s : N.State) (i : N.Inputs) :
  R.v44939 (state s) (inputs i) = Zmod.unsigned (N.v44939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44939 s i)) at 1.
  unfold R.v44939, N.v44939.
  rewrite ?node_44937.
  rewrite ?node_44938.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44940 (s : N.State) (i : N.Inputs) :
  R.v44940 (state s) (inputs i) = Zmod.unsigned (N.v44940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44940 s i)) at 1.
  unfold R.v44940, N.v44940.
  rewrite ?node_44936.
  rewrite ?node_44939.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44941 (s : N.State) (i : N.Inputs) :
  R.v44941 (state s) (inputs i) = Zmod.unsigned (N.v44941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44941 s i)) at 1.
  unfold R.v44941, N.v44941.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44942 (s : N.State) (i : N.Inputs) :
  R.v44942 (state s) (inputs i) = Zmod.unsigned (N.v44942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44942 s i)) at 1.
  unfold R.v44942, N.v44942.
  rewrite ?node_12434.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44943 (s : N.State) (i : N.Inputs) :
  R.v44943 (state s) (inputs i) = Zmod.unsigned (N.v44943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44943 s i)) at 1.
  unfold R.v44943, N.v44943.
  unfold R.v6, N.v6.
  rewrite ?node_12430.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44944 (s : N.State) (i : N.Inputs) :
  R.v44944 (state s) (inputs i) = Zmod.unsigned (N.v44944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44944 s i)) at 1.
  unfold R.v44944, N.v44944.
  unfold R.v6, N.v6.
  rewrite ?node_12423.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44945 (s : N.State) (i : N.Inputs) :
  R.v44945 (state s) (inputs i) = Zmod.unsigned (N.v44945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44945 s i)) at 1.
  unfold R.v44945, N.v44945.
  rewrite ?node_44943.
  rewrite ?node_44944.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44946 (s : N.State) (i : N.Inputs) :
  R.v44946 (state s) (inputs i) = Zmod.unsigned (N.v44946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44946 s i)) at 1.
  unfold R.v44946, N.v44946.
  unfold R.v16484, N.v16484.
  rewrite ?node_44945.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44947 (s : N.State) (i : N.Inputs) :
  R.v44947 (state s) (inputs i) = Zmod.unsigned (N.v44947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44947 s i)) at 1.
  unfold R.v44947, N.v44947.
  rewrite ?node_44942.
  rewrite ?node_44946.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44948 (s : N.State) (i : N.Inputs) :
  R.v44948 (state s) (inputs i) = Zmod.unsigned (N.v44948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44948 s i)) at 1.
  unfold R.v44948, N.v44948.
  unfold R.v6, N.v6.
  rewrite ?node_44947.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44949 (s : N.State) (i : N.Inputs) :
  R.v44949 (state s) (inputs i) = Zmod.unsigned (N.v44949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44949 s i)) at 1.
  unfold R.v44949, N.v44949.
  rewrite ?node_12435.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44950 (s : N.State) (i : N.Inputs) :
  R.v44950 (state s) (inputs i) = Zmod.unsigned (N.v44950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44950 s i)) at 1.
  unfold R.v44950, N.v44950.
  unfold R.v6, N.v6.
  rewrite ?node_12632.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44951 (s : N.State) (i : N.Inputs) :
  R.v44951 (state s) (inputs i) = Zmod.unsigned (N.v44951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44951 s i)) at 1.
  unfold R.v44951, N.v44951.
  rewrite ?node_44949.
  rewrite ?node_44950.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44952 (s : N.State) (i : N.Inputs) :
  R.v44952 (state s) (inputs i) = Zmod.unsigned (N.v44952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44952 s i)) at 1.
  unfold R.v44952, N.v44952.
  rewrite ?node_44948.
  rewrite ?node_44951.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44953 (s : N.State) (i : N.Inputs) :
  R.v44953 (state s) (inputs i) = Zmod.unsigned (N.v44953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44953 s i)) at 1.
  unfold R.v44953, N.v44953.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44954 (s : N.State) (i : N.Inputs) :
  R.v44954 (state s) (inputs i) = Zmod.unsigned (N.v44954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44954 s i)) at 1.
  unfold R.v44954, N.v44954.
  rewrite ?node_12460.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44955 (s : N.State) (i : N.Inputs) :
  R.v44955 (state s) (inputs i) = Zmod.unsigned (N.v44955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44955 s i)) at 1.
  unfold R.v44955, N.v44955.
  rewrite ?node_12456.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44956 (s : N.State) (i : N.Inputs) :
  R.v44956 (state s) (inputs i) = Zmod.unsigned (N.v44956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44956 s i)) at 1.
  unfold R.v44956, N.v44956.
  rewrite ?node_12452.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44957 (s : N.State) (i : N.Inputs) :
  R.v44957 (state s) (inputs i) = Zmod.unsigned (N.v44957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44957 s i)) at 1.
  unfold R.v44957, N.v44957.
  unfold R.v6, N.v6.
  rewrite ?node_12449.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44958 (s : N.State) (i : N.Inputs) :
  R.v44958 (state s) (inputs i) = Zmod.unsigned (N.v44958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44958 s i)) at 1.
  unfold R.v44958, N.v44958.
  unfold R.v6, N.v6.
  rewrite ?node_12442.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44959 (s : N.State) (i : N.Inputs) :
  R.v44959 (state s) (inputs i) = Zmod.unsigned (N.v44959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44959 s i)) at 1.
  unfold R.v44959, N.v44959.
  rewrite ?node_44957.
  rewrite ?node_44958.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44960 (s : N.State) (i : N.Inputs) :
  R.v44960 (state s) (inputs i) = Zmod.unsigned (N.v44960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44960 s i)) at 1.
  unfold R.v44960, N.v44960.
  unfold R.v16484, N.v16484.
  rewrite ?node_44959.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44961 (s : N.State) (i : N.Inputs) :
  R.v44961 (state s) (inputs i) = Zmod.unsigned (N.v44961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44961 s i)) at 1.
  unfold R.v44961, N.v44961.
  rewrite ?node_44954.
  rewrite ?node_44955.
  rewrite ?node_44956.
  rewrite ?node_44960.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44962 (s : N.State) (i : N.Inputs) :
  R.v44962 (state s) (inputs i) = Zmod.unsigned (N.v44962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44962 s i)) at 1.
  unfold R.v44962, N.v44962.
  unfold R.v6, N.v6.
  rewrite ?node_44961.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44963 (s : N.State) (i : N.Inputs) :
  R.v44963 (state s) (inputs i) = Zmod.unsigned (N.v44963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44963 s i)) at 1.
  unfold R.v44963, N.v44963.
  rewrite ?node_12461.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44964 (s : N.State) (i : N.Inputs) :
  R.v44964 (state s) (inputs i) = Zmod.unsigned (N.v44964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44964 s i)) at 1.
  unfold R.v44964, N.v44964.
  unfold R.v6, N.v6.
  rewrite ?node_12595.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44965 (s : N.State) (i : N.Inputs) :
  R.v44965 (state s) (inputs i) = Zmod.unsigned (N.v44965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44965 s i)) at 1.
  unfold R.v44965, N.v44965.
  unfold R.v6, N.v6.
  rewrite ?node_12635.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44966 (s : N.State) (i : N.Inputs) :
  R.v44966 (state s) (inputs i) = Zmod.unsigned (N.v44966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44966 s i)) at 1.
  unfold R.v44966, N.v44966.
  rewrite ?node_44963.
  rewrite ?node_44964.
  rewrite ?node_44965.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44967 (s : N.State) (i : N.Inputs) :
  R.v44967 (state s) (inputs i) = Zmod.unsigned (N.v44967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44967 s i)) at 1.
  unfold R.v44967, N.v44967.
  rewrite ?node_44962.
  rewrite ?node_44966.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44968 (s : N.State) (i : N.Inputs) :
  R.v44968 (state s) (inputs i) = Zmod.unsigned (N.v44968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44968 s i)) at 1.
  unfold R.v44968, N.v44968.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44969 (s : N.State) (i : N.Inputs) :
  R.v44969 (state s) (inputs i) = Zmod.unsigned (N.v44969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44969 s i)) at 1.
  unfold R.v44969, N.v44969.
  rewrite ?node_12452.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44970 (s : N.State) (i : N.Inputs) :
  R.v44970 (state s) (inputs i) = Zmod.unsigned (N.v44970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44970 s i)) at 1.
  unfold R.v44970, N.v44970.
  unfold R.v6, N.v6.
  rewrite ?node_12449.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44971 (s : N.State) (i : N.Inputs) :
  R.v44971 (state s) (inputs i) = Zmod.unsigned (N.v44971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44971 s i)) at 1.
  unfold R.v44971, N.v44971.
  unfold R.v6, N.v6.
  rewrite ?node_12442.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44972 (s : N.State) (i : N.Inputs) :
  R.v44972 (state s) (inputs i) = Zmod.unsigned (N.v44972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44972 s i)) at 1.
  unfold R.v44972, N.v44972.
  rewrite ?node_44970.
  rewrite ?node_44971.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44973 (s : N.State) (i : N.Inputs) :
  R.v44973 (state s) (inputs i) = Zmod.unsigned (N.v44973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44973 s i)) at 1.
  unfold R.v44973, N.v44973.
  unfold R.v16484, N.v16484.
  rewrite ?node_44972.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44974 (s : N.State) (i : N.Inputs) :
  R.v44974 (state s) (inputs i) = Zmod.unsigned (N.v44974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44974 s i)) at 1.
  unfold R.v44974, N.v44974.
  rewrite ?node_44969.
  rewrite ?node_44973.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44975 (s : N.State) (i : N.Inputs) :
  R.v44975 (state s) (inputs i) = Zmod.unsigned (N.v44975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44975 s i)) at 1.
  unfold R.v44975, N.v44975.
  unfold R.v6, N.v6.
  rewrite ?node_44974.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44976 (s : N.State) (i : N.Inputs) :
  R.v44976 (state s) (inputs i) = Zmod.unsigned (N.v44976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44976 s i)) at 1.
  unfold R.v44976, N.v44976.
  rewrite ?node_12453.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44977 (s : N.State) (i : N.Inputs) :
  R.v44977 (state s) (inputs i) = Zmod.unsigned (N.v44977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44977 s i)) at 1.
  unfold R.v44977, N.v44977.
  unfold R.v6, N.v6.
  rewrite ?node_12595.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44978 (s : N.State) (i : N.Inputs) :
  R.v44978 (state s) (inputs i) = Zmod.unsigned (N.v44978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44978 s i)) at 1.
  unfold R.v44978, N.v44978.
  rewrite ?node_44976.
  rewrite ?node_44977.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44979 (s : N.State) (i : N.Inputs) :
  R.v44979 (state s) (inputs i) = Zmod.unsigned (N.v44979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44979 s i)) at 1.
  unfold R.v44979, N.v44979.
  rewrite ?node_44975.
  rewrite ?node_44978.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44980 (s : N.State) (i : N.Inputs) :
  R.v44980 (state s) (inputs i) = Zmod.unsigned (N.v44980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44980 s i)) at 1.
  unfold R.v44980, N.v44980.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44981 (s : N.State) (i : N.Inputs) :
  R.v44981 (state s) (inputs i) = Zmod.unsigned (N.v44981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44981 s i)) at 1.
  unfold R.v44981, N.v44981.
  rewrite ?node_12460.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44982 (s : N.State) (i : N.Inputs) :
  R.v44982 (state s) (inputs i) = Zmod.unsigned (N.v44982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44982 s i)) at 1.
  unfold R.v44982, N.v44982.
  unfold R.v6, N.v6.
  rewrite ?node_12456.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44983 (s : N.State) (i : N.Inputs) :
  R.v44983 (state s) (inputs i) = Zmod.unsigned (N.v44983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44983 s i)) at 1.
  unfold R.v44983, N.v44983.
  unfold R.v6, N.v6.
  rewrite ?node_12453.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44984 (s : N.State) (i : N.Inputs) :
  R.v44984 (state s) (inputs i) = Zmod.unsigned (N.v44984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44984 s i)) at 1.
  unfold R.v44984, N.v44984.
  rewrite ?node_44982.
  rewrite ?node_44983.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44985 (s : N.State) (i : N.Inputs) :
  R.v44985 (state s) (inputs i) = Zmod.unsigned (N.v44985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44985 s i)) at 1.
  unfold R.v44985, N.v44985.
  unfold R.v16484, N.v16484.
  rewrite ?node_44984.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44986 (s : N.State) (i : N.Inputs) :
  R.v44986 (state s) (inputs i) = Zmod.unsigned (N.v44986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44986 s i)) at 1.
  unfold R.v44986, N.v44986.
  rewrite ?node_44981.
  rewrite ?node_44985.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44987 (s : N.State) (i : N.Inputs) :
  R.v44987 (state s) (inputs i) = Zmod.unsigned (N.v44987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44987 s i)) at 1.
  unfold R.v44987, N.v44987.
  unfold R.v6, N.v6.
  rewrite ?node_44986.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44988 (s : N.State) (i : N.Inputs) :
  R.v44988 (state s) (inputs i) = Zmod.unsigned (N.v44988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44988 s i)) at 1.
  unfold R.v44988, N.v44988.
  rewrite ?node_12461.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44989 (s : N.State) (i : N.Inputs) :
  R.v44989 (state s) (inputs i) = Zmod.unsigned (N.v44989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44989 s i)) at 1.
  unfold R.v44989, N.v44989.
  unfold R.v6, N.v6.
  rewrite ?node_12635.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44990 (s : N.State) (i : N.Inputs) :
  R.v44990 (state s) (inputs i) = Zmod.unsigned (N.v44990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44990 s i)) at 1.
  unfold R.v44990, N.v44990.
  rewrite ?node_44988.
  rewrite ?node_44989.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44991 (s : N.State) (i : N.Inputs) :
  R.v44991 (state s) (inputs i) = Zmod.unsigned (N.v44991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44991 s i)) at 1.
  unfold R.v44991, N.v44991.
  rewrite ?node_44987.
  rewrite ?node_44990.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44992 (s : N.State) (i : N.Inputs) :
  R.v44992 (state s) (inputs i) = Zmod.unsigned (N.v44992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44992 s i)) at 1.
  unfold R.v44992, N.v44992.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44993 (s : N.State) (i : N.Inputs) :
  R.v44993 (state s) (inputs i) = Zmod.unsigned (N.v44993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44993 s i)) at 1.
  unfold R.v44993, N.v44993.
  rewrite ?node_12480.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44994 (s : N.State) (i : N.Inputs) :
  R.v44994 (state s) (inputs i) = Zmod.unsigned (N.v44994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44994 s i)) at 1.
  unfold R.v44994, N.v44994.
  rewrite ?node_12476.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44995 (s : N.State) (i : N.Inputs) :
  R.v44995 (state s) (inputs i) = Zmod.unsigned (N.v44995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44995 s i)) at 1.
  unfold R.v44995, N.v44995.
  rewrite ?node_12472.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44996 (s : N.State) (i : N.Inputs) :
  R.v44996 (state s) (inputs i) = Zmod.unsigned (N.v44996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44996 s i)) at 1.
  unfold R.v44996, N.v44996.
  unfold R.v6, N.v6.
  rewrite ?node_12468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44997 (s : N.State) (i : N.Inputs) :
  R.v44997 (state s) (inputs i) = Zmod.unsigned (N.v44997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44997 s i)) at 1.
  unfold R.v44997, N.v44997.
  unfold R.v6, N.v6.
  rewrite ?node_12465.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44998 (s : N.State) (i : N.Inputs) :
  R.v44998 (state s) (inputs i) = Zmod.unsigned (N.v44998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44998 s i)) at 1.
  unfold R.v44998, N.v44998.
  rewrite ?node_44996.
  rewrite ?node_44997.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_44999 (s : N.State) (i : N.Inputs) :
  R.v44999 (state s) (inputs i) = Zmod.unsigned (N.v44999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v44999 s i)) at 1.
  unfold R.v44999, N.v44999.
  unfold R.v16484, N.v16484.
  rewrite ?node_44998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
