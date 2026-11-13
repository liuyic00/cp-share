(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes047.
Lemma node_48000 (s : N.State) (i : N.Inputs) :
  R.v48000 (state s) (inputs i) = Zmod.unsigned (N.v48000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48000 s i)) at 1.
  unfold R.v48000, N.v48000.
  unfold R.v16484, N.v16484.
  rewrite ?node_47999.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48001 (s : N.State) (i : N.Inputs) :
  R.v48001 (state s) (inputs i) = Zmod.unsigned (N.v48001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48001 s i)) at 1.
  unfold R.v48001, N.v48001.
  rewrite ?node_47996.
  rewrite ?node_48000.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48002 (s : N.State) (i : N.Inputs) :
  R.v48002 (state s) (inputs i) = Zmod.unsigned (N.v48002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48002 s i)) at 1.
  unfold R.v48002, N.v48002.
  unfold R.v6, N.v6.
  rewrite ?node_48001.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48003 (s : N.State) (i : N.Inputs) :
  R.v48003 (state s) (inputs i) = Zmod.unsigned (N.v48003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48003 s i)) at 1.
  unfold R.v48003, N.v48003.
  rewrite ?node_15549.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48004 (s : N.State) (i : N.Inputs) :
  R.v48004 (state s) (inputs i) = Zmod.unsigned (N.v48004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48004 s i)) at 1.
  unfold R.v48004, N.v48004.
  unfold R.v6, N.v6.
  rewrite ?node_15610.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48005 (s : N.State) (i : N.Inputs) :
  R.v48005 (state s) (inputs i) = Zmod.unsigned (N.v48005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48005 s i)) at 1.
  unfold R.v48005, N.v48005.
  rewrite ?node_48003.
  rewrite ?node_48004.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48006 (s : N.State) (i : N.Inputs) :
  R.v48006 (state s) (inputs i) = Zmod.unsigned (N.v48006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48006 s i)) at 1.
  unfold R.v48006, N.v48006.
  rewrite ?node_48002.
  rewrite ?node_48005.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48007 (s : N.State) (i : N.Inputs) :
  R.v48007 (state s) (inputs i) = Zmod.unsigned (N.v48007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48007 s i)) at 1.
  unfold R.v48007, N.v48007.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48008 (s : N.State) (i : N.Inputs) :
  R.v48008 (state s) (inputs i) = Zmod.unsigned (N.v48008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48008 s i)) at 1.
  unfold R.v48008, N.v48008.
  rewrite ?node_15594.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48009 (s : N.State) (i : N.Inputs) :
  R.v48009 (state s) (inputs i) = Zmod.unsigned (N.v48009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48009 s i)) at 1.
  unfold R.v48009, N.v48009.
  rewrite ?node_15590.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48010 (s : N.State) (i : N.Inputs) :
  R.v48010 (state s) (inputs i) = Zmod.unsigned (N.v48010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48010 s i)) at 1.
  unfold R.v48010, N.v48010.
  rewrite ?node_15586.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48011 (s : N.State) (i : N.Inputs) :
  R.v48011 (state s) (inputs i) = Zmod.unsigned (N.v48011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48011 s i)) at 1.
  unfold R.v48011, N.v48011.
  unfold R.v6, N.v6.
  rewrite ?node_15583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48012 (s : N.State) (i : N.Inputs) :
  R.v48012 (state s) (inputs i) = Zmod.unsigned (N.v48012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48012 s i)) at 1.
  unfold R.v48012, N.v48012.
  unfold R.v6, N.v6.
  rewrite ?node_15576.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48013 (s : N.State) (i : N.Inputs) :
  R.v48013 (state s) (inputs i) = Zmod.unsigned (N.v48013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48013 s i)) at 1.
  unfold R.v48013, N.v48013.
  rewrite ?node_48011.
  rewrite ?node_48012.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48014 (s : N.State) (i : N.Inputs) :
  R.v48014 (state s) (inputs i) = Zmod.unsigned (N.v48014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48014 s i)) at 1.
  unfold R.v48014, N.v48014.
  unfold R.v16484, N.v16484.
  rewrite ?node_48013.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48015 (s : N.State) (i : N.Inputs) :
  R.v48015 (state s) (inputs i) = Zmod.unsigned (N.v48015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48015 s i)) at 1.
  unfold R.v48015, N.v48015.
  rewrite ?node_48008.
  rewrite ?node_48009.
  rewrite ?node_48010.
  rewrite ?node_48014.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48016 (s : N.State) (i : N.Inputs) :
  R.v48016 (state s) (inputs i) = Zmod.unsigned (N.v48016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48016 s i)) at 1.
  unfold R.v48016, N.v48016.
  unfold R.v6, N.v6.
  rewrite ?node_48015.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48017 (s : N.State) (i : N.Inputs) :
  R.v48017 (state s) (inputs i) = Zmod.unsigned (N.v48017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48017 s i)) at 1.
  unfold R.v48017, N.v48017.
  rewrite ?node_15595.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48018 (s : N.State) (i : N.Inputs) :
  R.v48018 (state s) (inputs i) = Zmod.unsigned (N.v48018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48018 s i)) at 1.
  unfold R.v48018, N.v48018.
  unfold R.v6, N.v6.
  rewrite ?node_15647.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48019 (s : N.State) (i : N.Inputs) :
  R.v48019 (state s) (inputs i) = Zmod.unsigned (N.v48019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48019 s i)) at 1.
  unfold R.v48019, N.v48019.
  unfold R.v6, N.v6.
  rewrite ?node_15659.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48020 (s : N.State) (i : N.Inputs) :
  R.v48020 (state s) (inputs i) = Zmod.unsigned (N.v48020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48020 s i)) at 1.
  unfold R.v48020, N.v48020.
  rewrite ?node_48017.
  rewrite ?node_48018.
  rewrite ?node_48019.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48021 (s : N.State) (i : N.Inputs) :
  R.v48021 (state s) (inputs i) = Zmod.unsigned (N.v48021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48021 s i)) at 1.
  unfold R.v48021, N.v48021.
  rewrite ?node_48016.
  rewrite ?node_48020.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48022 (s : N.State) (i : N.Inputs) :
  R.v48022 (state s) (inputs i) = Zmod.unsigned (N.v48022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48022 s i)) at 1.
  unfold R.v48022, N.v48022.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48023 (s : N.State) (i : N.Inputs) :
  R.v48023 (state s) (inputs i) = Zmod.unsigned (N.v48023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48023 s i)) at 1.
  unfold R.v48023, N.v48023.
  rewrite ?node_15586.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48024 (s : N.State) (i : N.Inputs) :
  R.v48024 (state s) (inputs i) = Zmod.unsigned (N.v48024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48024 s i)) at 1.
  unfold R.v48024, N.v48024.
  unfold R.v6, N.v6.
  rewrite ?node_15583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48025 (s : N.State) (i : N.Inputs) :
  R.v48025 (state s) (inputs i) = Zmod.unsigned (N.v48025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48025 s i)) at 1.
  unfold R.v48025, N.v48025.
  unfold R.v6, N.v6.
  rewrite ?node_15576.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48026 (s : N.State) (i : N.Inputs) :
  R.v48026 (state s) (inputs i) = Zmod.unsigned (N.v48026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48026 s i)) at 1.
  unfold R.v48026, N.v48026.
  rewrite ?node_48024.
  rewrite ?node_48025.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48027 (s : N.State) (i : N.Inputs) :
  R.v48027 (state s) (inputs i) = Zmod.unsigned (N.v48027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48027 s i)) at 1.
  unfold R.v48027, N.v48027.
  unfold R.v16484, N.v16484.
  rewrite ?node_48026.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48028 (s : N.State) (i : N.Inputs) :
  R.v48028 (state s) (inputs i) = Zmod.unsigned (N.v48028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48028 s i)) at 1.
  unfold R.v48028, N.v48028.
  rewrite ?node_48023.
  rewrite ?node_48027.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48029 (s : N.State) (i : N.Inputs) :
  R.v48029 (state s) (inputs i) = Zmod.unsigned (N.v48029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48029 s i)) at 1.
  unfold R.v48029, N.v48029.
  unfold R.v6, N.v6.
  rewrite ?node_48028.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48030 (s : N.State) (i : N.Inputs) :
  R.v48030 (state s) (inputs i) = Zmod.unsigned (N.v48030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48030 s i)) at 1.
  unfold R.v48030, N.v48030.
  rewrite ?node_15587.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48031 (s : N.State) (i : N.Inputs) :
  R.v48031 (state s) (inputs i) = Zmod.unsigned (N.v48031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48031 s i)) at 1.
  unfold R.v48031, N.v48031.
  unfold R.v6, N.v6.
  rewrite ?node_15647.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48032 (s : N.State) (i : N.Inputs) :
  R.v48032 (state s) (inputs i) = Zmod.unsigned (N.v48032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48032 s i)) at 1.
  unfold R.v48032, N.v48032.
  rewrite ?node_48030.
  rewrite ?node_48031.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48033 (s : N.State) (i : N.Inputs) :
  R.v48033 (state s) (inputs i) = Zmod.unsigned (N.v48033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48033 s i)) at 1.
  unfold R.v48033, N.v48033.
  rewrite ?node_48029.
  rewrite ?node_48032.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48034 (s : N.State) (i : N.Inputs) :
  R.v48034 (state s) (inputs i) = Zmod.unsigned (N.v48034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48034 s i)) at 1.
  unfold R.v48034, N.v48034.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48035 (s : N.State) (i : N.Inputs) :
  R.v48035 (state s) (inputs i) = Zmod.unsigned (N.v48035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48035 s i)) at 1.
  unfold R.v48035, N.v48035.
  rewrite ?node_15594.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48036 (s : N.State) (i : N.Inputs) :
  R.v48036 (state s) (inputs i) = Zmod.unsigned (N.v48036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48036 s i)) at 1.
  unfold R.v48036, N.v48036.
  unfold R.v6, N.v6.
  rewrite ?node_15590.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48037 (s : N.State) (i : N.Inputs) :
  R.v48037 (state s) (inputs i) = Zmod.unsigned (N.v48037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48037 s i)) at 1.
  unfold R.v48037, N.v48037.
  unfold R.v6, N.v6.
  rewrite ?node_15587.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48038 (s : N.State) (i : N.Inputs) :
  R.v48038 (state s) (inputs i) = Zmod.unsigned (N.v48038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48038 s i)) at 1.
  unfold R.v48038, N.v48038.
  rewrite ?node_48036.
  rewrite ?node_48037.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48039 (s : N.State) (i : N.Inputs) :
  R.v48039 (state s) (inputs i) = Zmod.unsigned (N.v48039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48039 s i)) at 1.
  unfold R.v48039, N.v48039.
  unfold R.v16484, N.v16484.
  rewrite ?node_48038.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48040 (s : N.State) (i : N.Inputs) :
  R.v48040 (state s) (inputs i) = Zmod.unsigned (N.v48040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48040 s i)) at 1.
  unfold R.v48040, N.v48040.
  rewrite ?node_48035.
  rewrite ?node_48039.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48041 (s : N.State) (i : N.Inputs) :
  R.v48041 (state s) (inputs i) = Zmod.unsigned (N.v48041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48041 s i)) at 1.
  unfold R.v48041, N.v48041.
  unfold R.v6, N.v6.
  rewrite ?node_48040.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48042 (s : N.State) (i : N.Inputs) :
  R.v48042 (state s) (inputs i) = Zmod.unsigned (N.v48042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48042 s i)) at 1.
  unfold R.v48042, N.v48042.
  rewrite ?node_15595.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48043 (s : N.State) (i : N.Inputs) :
  R.v48043 (state s) (inputs i) = Zmod.unsigned (N.v48043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48043 s i)) at 1.
  unfold R.v48043, N.v48043.
  unfold R.v6, N.v6.
  rewrite ?node_15659.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48044 (s : N.State) (i : N.Inputs) :
  R.v48044 (state s) (inputs i) = Zmod.unsigned (N.v48044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48044 s i)) at 1.
  unfold R.v48044, N.v48044.
  rewrite ?node_48042.
  rewrite ?node_48043.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48045 (s : N.State) (i : N.Inputs) :
  R.v48045 (state s) (inputs i) = Zmod.unsigned (N.v48045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48045 s i)) at 1.
  unfold R.v48045, N.v48045.
  rewrite ?node_48041.
  rewrite ?node_48044.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48046 (s : N.State) (i : N.Inputs) :
  R.v48046 (state s) (inputs i) = Zmod.unsigned (N.v48046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48046 s i)) at 1.
  unfold R.v48046, N.v48046.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48047 (s : N.State) (i : N.Inputs) :
  R.v48047 (state s) (inputs i) = Zmod.unsigned (N.v48047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48047 s i)) at 1.
  unfold R.v48047, N.v48047.
  unfold R.v6, N.v6.
  rewrite ?node_15601.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48048 (s : N.State) (i : N.Inputs) :
  R.v48048 (state s) (inputs i) = Zmod.unsigned (N.v48048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48048 s i)) at 1.
  unfold R.v48048, N.v48048.
  unfold R.v6, N.v6.
  rewrite ?node_15598.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48049 (s : N.State) (i : N.Inputs) :
  R.v48049 (state s) (inputs i) = Zmod.unsigned (N.v48049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48049 s i)) at 1.
  unfold R.v48049, N.v48049.
  rewrite ?node_48047.
  rewrite ?node_48048.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48050 (s : N.State) (i : N.Inputs) :
  R.v48050 (state s) (inputs i) = Zmod.unsigned (N.v48050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48050 s i)) at 1.
  unfold R.v48050, N.v48050.
  unfold R.v16463, N.v16463.
  rewrite ?node_48049.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48051 (s : N.State) (i : N.Inputs) :
  R.v48051 (state s) (inputs i) = Zmod.unsigned (N.v48051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48051 s i)) at 1.
  unfold R.v48051, N.v48051.
  rewrite ?node_15602.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48052 (s : N.State) (i : N.Inputs) :
  R.v48052 (state s) (inputs i) = Zmod.unsigned (N.v48052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48052 s i)) at 1.
  unfold R.v48052, N.v48052.
  unfold R.v6, N.v6.
  rewrite ?node_15661.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48053 (s : N.State) (i : N.Inputs) :
  R.v48053 (state s) (inputs i) = Zmod.unsigned (N.v48053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48053 s i)) at 1.
  unfold R.v48053, N.v48053.
  rewrite ?node_48051.
  rewrite ?node_48052.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48054 (s : N.State) (i : N.Inputs) :
  R.v48054 (state s) (inputs i) = Zmod.unsigned (N.v48054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48054 s i)) at 1.
  unfold R.v48054, N.v48054.
  rewrite ?node_48050.
  rewrite ?node_48053.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48055 (s : N.State) (i : N.Inputs) :
  R.v48055 (state s) (inputs i) = Zmod.unsigned (N.v48055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48055 s i)) at 1.
  unfold R.v48055, N.v48055.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48056 (s : N.State) (i : N.Inputs) :
  R.v48056 (state s) (inputs i) = Zmod.unsigned (N.v48056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48056 s i)) at 1.
  unfold R.v48056, N.v48056.
  rewrite ?node_15647.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48057 (s : N.State) (i : N.Inputs) :
  R.v48057 (state s) (inputs i) = Zmod.unsigned (N.v48057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48057 s i)) at 1.
  unfold R.v48057, N.v48057.
  rewrite ?node_15643.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48058 (s : N.State) (i : N.Inputs) :
  R.v48058 (state s) (inputs i) = Zmod.unsigned (N.v48058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48058 s i)) at 1.
  unfold R.v48058, N.v48058.
  rewrite ?node_15639.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48059 (s : N.State) (i : N.Inputs) :
  R.v48059 (state s) (inputs i) = Zmod.unsigned (N.v48059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48059 s i)) at 1.
  unfold R.v48059, N.v48059.
  unfold R.v6, N.v6.
  rewrite ?node_15637.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48060 (s : N.State) (i : N.Inputs) :
  R.v48060 (state s) (inputs i) = Zmod.unsigned (N.v48060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48060 s i)) at 1.
  unfold R.v48060, N.v48060.
  unfold R.v6, N.v6.
  rewrite ?node_15630.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48061 (s : N.State) (i : N.Inputs) :
  R.v48061 (state s) (inputs i) = Zmod.unsigned (N.v48061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48061 s i)) at 1.
  unfold R.v48061, N.v48061.
  rewrite ?node_48059.
  rewrite ?node_48060.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48062 (s : N.State) (i : N.Inputs) :
  R.v48062 (state s) (inputs i) = Zmod.unsigned (N.v48062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48062 s i)) at 1.
  unfold R.v48062, N.v48062.
  unfold R.v16484, N.v16484.
  rewrite ?node_48061.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48063 (s : N.State) (i : N.Inputs) :
  R.v48063 (state s) (inputs i) = Zmod.unsigned (N.v48063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48063 s i)) at 1.
  unfold R.v48063, N.v48063.
  rewrite ?node_48056.
  rewrite ?node_48057.
  rewrite ?node_48058.
  rewrite ?node_48062.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48064 (s : N.State) (i : N.Inputs) :
  R.v48064 (state s) (inputs i) = Zmod.unsigned (N.v48064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48064 s i)) at 1.
  unfold R.v48064, N.v48064.
  unfold R.v6, N.v6.
  rewrite ?node_48063.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48065 (s : N.State) (i : N.Inputs) :
  R.v48065 (state s) (inputs i) = Zmod.unsigned (N.v48065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48065 s i)) at 1.
  unfold R.v48065, N.v48065.
  rewrite ?node_15648.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48066 (s : N.State) (i : N.Inputs) :
  R.v48066 (state s) (inputs i) = Zmod.unsigned (N.v48066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48066 s i)) at 1.
  unfold R.v48066, N.v48066.
  unfold R.v6, N.v6.
  rewrite ?node_15699.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48067 (s : N.State) (i : N.Inputs) :
  R.v48067 (state s) (inputs i) = Zmod.unsigned (N.v48067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48067 s i)) at 1.
  unfold R.v48067, N.v48067.
  unfold R.v6, N.v6.
  rewrite ?node_15709.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48068 (s : N.State) (i : N.Inputs) :
  R.v48068 (state s) (inputs i) = Zmod.unsigned (N.v48068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48068 s i)) at 1.
  unfold R.v48068, N.v48068.
  rewrite ?node_48065.
  rewrite ?node_48066.
  rewrite ?node_48067.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48069 (s : N.State) (i : N.Inputs) :
  R.v48069 (state s) (inputs i) = Zmod.unsigned (N.v48069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48069 s i)) at 1.
  unfold R.v48069, N.v48069.
  rewrite ?node_48064.
  rewrite ?node_48068.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48070 (s : N.State) (i : N.Inputs) :
  R.v48070 (state s) (inputs i) = Zmod.unsigned (N.v48070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48070 s i)) at 1.
  unfold R.v48070, N.v48070.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48071 (s : N.State) (i : N.Inputs) :
  R.v48071 (state s) (inputs i) = Zmod.unsigned (N.v48071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48071 s i)) at 1.
  unfold R.v48071, N.v48071.
  rewrite ?node_15639.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48072 (s : N.State) (i : N.Inputs) :
  R.v48072 (state s) (inputs i) = Zmod.unsigned (N.v48072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48072 s i)) at 1.
  unfold R.v48072, N.v48072.
  unfold R.v6, N.v6.
  rewrite ?node_15637.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48073 (s : N.State) (i : N.Inputs) :
  R.v48073 (state s) (inputs i) = Zmod.unsigned (N.v48073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48073 s i)) at 1.
  unfold R.v48073, N.v48073.
  unfold R.v6, N.v6.
  rewrite ?node_15630.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48074 (s : N.State) (i : N.Inputs) :
  R.v48074 (state s) (inputs i) = Zmod.unsigned (N.v48074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48074 s i)) at 1.
  unfold R.v48074, N.v48074.
  rewrite ?node_48072.
  rewrite ?node_48073.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48075 (s : N.State) (i : N.Inputs) :
  R.v48075 (state s) (inputs i) = Zmod.unsigned (N.v48075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48075 s i)) at 1.
  unfold R.v48075, N.v48075.
  unfold R.v16484, N.v16484.
  rewrite ?node_48074.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48076 (s : N.State) (i : N.Inputs) :
  R.v48076 (state s) (inputs i) = Zmod.unsigned (N.v48076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48076 s i)) at 1.
  unfold R.v48076, N.v48076.
  rewrite ?node_48071.
  rewrite ?node_48075.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48077 (s : N.State) (i : N.Inputs) :
  R.v48077 (state s) (inputs i) = Zmod.unsigned (N.v48077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48077 s i)) at 1.
  unfold R.v48077, N.v48077.
  unfold R.v6, N.v6.
  rewrite ?node_48076.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48078 (s : N.State) (i : N.Inputs) :
  R.v48078 (state s) (inputs i) = Zmod.unsigned (N.v48078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48078 s i)) at 1.
  unfold R.v48078, N.v48078.
  rewrite ?node_15640.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48079 (s : N.State) (i : N.Inputs) :
  R.v48079 (state s) (inputs i) = Zmod.unsigned (N.v48079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48079 s i)) at 1.
  unfold R.v48079, N.v48079.
  unfold R.v6, N.v6.
  rewrite ?node_15699.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48080 (s : N.State) (i : N.Inputs) :
  R.v48080 (state s) (inputs i) = Zmod.unsigned (N.v48080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48080 s i)) at 1.
  unfold R.v48080, N.v48080.
  rewrite ?node_48078.
  rewrite ?node_48079.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48081 (s : N.State) (i : N.Inputs) :
  R.v48081 (state s) (inputs i) = Zmod.unsigned (N.v48081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48081 s i)) at 1.
  unfold R.v48081, N.v48081.
  rewrite ?node_48077.
  rewrite ?node_48080.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48082 (s : N.State) (i : N.Inputs) :
  R.v48082 (state s) (inputs i) = Zmod.unsigned (N.v48082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48082 s i)) at 1.
  unfold R.v48082, N.v48082.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48083 (s : N.State) (i : N.Inputs) :
  R.v48083 (state s) (inputs i) = Zmod.unsigned (N.v48083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48083 s i)) at 1.
  unfold R.v48083, N.v48083.
  rewrite ?node_15647.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48084 (s : N.State) (i : N.Inputs) :
  R.v48084 (state s) (inputs i) = Zmod.unsigned (N.v48084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48084 s i)) at 1.
  unfold R.v48084, N.v48084.
  unfold R.v6, N.v6.
  rewrite ?node_15643.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48085 (s : N.State) (i : N.Inputs) :
  R.v48085 (state s) (inputs i) = Zmod.unsigned (N.v48085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48085 s i)) at 1.
  unfold R.v48085, N.v48085.
  unfold R.v6, N.v6.
  rewrite ?node_15640.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48086 (s : N.State) (i : N.Inputs) :
  R.v48086 (state s) (inputs i) = Zmod.unsigned (N.v48086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48086 s i)) at 1.
  unfold R.v48086, N.v48086.
  rewrite ?node_48084.
  rewrite ?node_48085.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48087 (s : N.State) (i : N.Inputs) :
  R.v48087 (state s) (inputs i) = Zmod.unsigned (N.v48087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48087 s i)) at 1.
  unfold R.v48087, N.v48087.
  unfold R.v16484, N.v16484.
  rewrite ?node_48086.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48088 (s : N.State) (i : N.Inputs) :
  R.v48088 (state s) (inputs i) = Zmod.unsigned (N.v48088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48088 s i)) at 1.
  unfold R.v48088, N.v48088.
  rewrite ?node_48083.
  rewrite ?node_48087.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48089 (s : N.State) (i : N.Inputs) :
  R.v48089 (state s) (inputs i) = Zmod.unsigned (N.v48089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48089 s i)) at 1.
  unfold R.v48089, N.v48089.
  unfold R.v6, N.v6.
  rewrite ?node_48088.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48090 (s : N.State) (i : N.Inputs) :
  R.v48090 (state s) (inputs i) = Zmod.unsigned (N.v48090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48090 s i)) at 1.
  unfold R.v48090, N.v48090.
  rewrite ?node_15648.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48091 (s : N.State) (i : N.Inputs) :
  R.v48091 (state s) (inputs i) = Zmod.unsigned (N.v48091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48091 s i)) at 1.
  unfold R.v48091, N.v48091.
  unfold R.v6, N.v6.
  rewrite ?node_15709.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48092 (s : N.State) (i : N.Inputs) :
  R.v48092 (state s) (inputs i) = Zmod.unsigned (N.v48092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48092 s i)) at 1.
  unfold R.v48092, N.v48092.
  rewrite ?node_48090.
  rewrite ?node_48091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48093 (s : N.State) (i : N.Inputs) :
  R.v48093 (state s) (inputs i) = Zmod.unsigned (N.v48093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48093 s i)) at 1.
  unfold R.v48093, N.v48093.
  rewrite ?node_48089.
  rewrite ?node_48092.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48094 (s : N.State) (i : N.Inputs) :
  R.v48094 (state s) (inputs i) = Zmod.unsigned (N.v48094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48094 s i)) at 1.
  unfold R.v48094, N.v48094.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48095 (s : N.State) (i : N.Inputs) :
  R.v48095 (state s) (inputs i) = Zmod.unsigned (N.v48095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48095 s i)) at 1.
  unfold R.v48095, N.v48095.
  unfold R.v6, N.v6.
  rewrite ?node_15654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48096 (s : N.State) (i : N.Inputs) :
  R.v48096 (state s) (inputs i) = Zmod.unsigned (N.v48096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48096 s i)) at 1.
  unfold R.v48096, N.v48096.
  unfold R.v6, N.v6.
  rewrite ?node_15651.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48097 (s : N.State) (i : N.Inputs) :
  R.v48097 (state s) (inputs i) = Zmod.unsigned (N.v48097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48097 s i)) at 1.
  unfold R.v48097, N.v48097.
  rewrite ?node_48095.
  rewrite ?node_48096.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48098 (s : N.State) (i : N.Inputs) :
  R.v48098 (state s) (inputs i) = Zmod.unsigned (N.v48098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48098 s i)) at 1.
  unfold R.v48098, N.v48098.
  unfold R.v16463, N.v16463.
  rewrite ?node_48097.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48099 (s : N.State) (i : N.Inputs) :
  R.v48099 (state s) (inputs i) = Zmod.unsigned (N.v48099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48099 s i)) at 1.
  unfold R.v48099, N.v48099.
  rewrite ?node_15655.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48100 (s : N.State) (i : N.Inputs) :
  R.v48100 (state s) (inputs i) = Zmod.unsigned (N.v48100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48100 s i)) at 1.
  unfold R.v48100, N.v48100.
  unfold R.v6, N.v6.
  rewrite ?node_15711.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48101 (s : N.State) (i : N.Inputs) :
  R.v48101 (state s) (inputs i) = Zmod.unsigned (N.v48101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48101 s i)) at 1.
  unfold R.v48101, N.v48101.
  rewrite ?node_48099.
  rewrite ?node_48100.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48102 (s : N.State) (i : N.Inputs) :
  R.v48102 (state s) (inputs i) = Zmod.unsigned (N.v48102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48102 s i)) at 1.
  unfold R.v48102, N.v48102.
  rewrite ?node_48098.
  rewrite ?node_48101.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48103 (s : N.State) (i : N.Inputs) :
  R.v48103 (state s) (inputs i) = Zmod.unsigned (N.v48103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48103 s i)) at 1.
  unfold R.v48103, N.v48103.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48104 (s : N.State) (i : N.Inputs) :
  R.v48104 (state s) (inputs i) = Zmod.unsigned (N.v48104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48104 s i)) at 1.
  unfold R.v48104, N.v48104.
  rewrite ?node_15699.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48105 (s : N.State) (i : N.Inputs) :
  R.v48105 (state s) (inputs i) = Zmod.unsigned (N.v48105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48105 s i)) at 1.
  unfold R.v48105, N.v48105.
  rewrite ?node_15695.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48106 (s : N.State) (i : N.Inputs) :
  R.v48106 (state s) (inputs i) = Zmod.unsigned (N.v48106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48106 s i)) at 1.
  unfold R.v48106, N.v48106.
  rewrite ?node_15691.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48107 (s : N.State) (i : N.Inputs) :
  R.v48107 (state s) (inputs i) = Zmod.unsigned (N.v48107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48107 s i)) at 1.
  unfold R.v48107, N.v48107.
  unfold R.v6, N.v6.
  rewrite ?node_15689.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48108 (s : N.State) (i : N.Inputs) :
  R.v48108 (state s) (inputs i) = Zmod.unsigned (N.v48108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48108 s i)) at 1.
  unfold R.v48108, N.v48108.
  unfold R.v6, N.v6.
  rewrite ?node_15682.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48109 (s : N.State) (i : N.Inputs) :
  R.v48109 (state s) (inputs i) = Zmod.unsigned (N.v48109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48109 s i)) at 1.
  unfold R.v48109, N.v48109.
  rewrite ?node_48107.
  rewrite ?node_48108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48110 (s : N.State) (i : N.Inputs) :
  R.v48110 (state s) (inputs i) = Zmod.unsigned (N.v48110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48110 s i)) at 1.
  unfold R.v48110, N.v48110.
  unfold R.v16484, N.v16484.
  rewrite ?node_48109.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48111 (s : N.State) (i : N.Inputs) :
  R.v48111 (state s) (inputs i) = Zmod.unsigned (N.v48111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48111 s i)) at 1.
  unfold R.v48111, N.v48111.
  rewrite ?node_48104.
  rewrite ?node_48105.
  rewrite ?node_48106.
  rewrite ?node_48110.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48112 (s : N.State) (i : N.Inputs) :
  R.v48112 (state s) (inputs i) = Zmod.unsigned (N.v48112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48112 s i)) at 1.
  unfold R.v48112, N.v48112.
  unfold R.v6, N.v6.
  rewrite ?node_48111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48113 (s : N.State) (i : N.Inputs) :
  R.v48113 (state s) (inputs i) = Zmod.unsigned (N.v48113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48113 s i)) at 1.
  unfold R.v48113, N.v48113.
  rewrite ?node_15700.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48114 (s : N.State) (i : N.Inputs) :
  R.v48114 (state s) (inputs i) = Zmod.unsigned (N.v48114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48114 s i)) at 1.
  unfold R.v48114, N.v48114.
  unfold R.v6, N.v6.
  rewrite ?node_15747.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48115 (s : N.State) (i : N.Inputs) :
  R.v48115 (state s) (inputs i) = Zmod.unsigned (N.v48115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48115 s i)) at 1.
  unfold R.v48115, N.v48115.
  unfold R.v6, N.v6.
  rewrite ?node_15757.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48116 (s : N.State) (i : N.Inputs) :
  R.v48116 (state s) (inputs i) = Zmod.unsigned (N.v48116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48116 s i)) at 1.
  unfold R.v48116, N.v48116.
  rewrite ?node_48113.
  rewrite ?node_48114.
  rewrite ?node_48115.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48117 (s : N.State) (i : N.Inputs) :
  R.v48117 (state s) (inputs i) = Zmod.unsigned (N.v48117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48117 s i)) at 1.
  unfold R.v48117, N.v48117.
  rewrite ?node_48112.
  rewrite ?node_48116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48118 (s : N.State) (i : N.Inputs) :
  R.v48118 (state s) (inputs i) = Zmod.unsigned (N.v48118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48118 s i)) at 1.
  unfold R.v48118, N.v48118.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48119 (s : N.State) (i : N.Inputs) :
  R.v48119 (state s) (inputs i) = Zmod.unsigned (N.v48119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48119 s i)) at 1.
  unfold R.v48119, N.v48119.
  rewrite ?node_15691.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48120 (s : N.State) (i : N.Inputs) :
  R.v48120 (state s) (inputs i) = Zmod.unsigned (N.v48120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48120 s i)) at 1.
  unfold R.v48120, N.v48120.
  unfold R.v6, N.v6.
  rewrite ?node_15689.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48121 (s : N.State) (i : N.Inputs) :
  R.v48121 (state s) (inputs i) = Zmod.unsigned (N.v48121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48121 s i)) at 1.
  unfold R.v48121, N.v48121.
  unfold R.v6, N.v6.
  rewrite ?node_15682.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48122 (s : N.State) (i : N.Inputs) :
  R.v48122 (state s) (inputs i) = Zmod.unsigned (N.v48122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48122 s i)) at 1.
  unfold R.v48122, N.v48122.
  rewrite ?node_48120.
  rewrite ?node_48121.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48123 (s : N.State) (i : N.Inputs) :
  R.v48123 (state s) (inputs i) = Zmod.unsigned (N.v48123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48123 s i)) at 1.
  unfold R.v48123, N.v48123.
  unfold R.v16484, N.v16484.
  rewrite ?node_48122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48124 (s : N.State) (i : N.Inputs) :
  R.v48124 (state s) (inputs i) = Zmod.unsigned (N.v48124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48124 s i)) at 1.
  unfold R.v48124, N.v48124.
  rewrite ?node_48119.
  rewrite ?node_48123.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48125 (s : N.State) (i : N.Inputs) :
  R.v48125 (state s) (inputs i) = Zmod.unsigned (N.v48125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48125 s i)) at 1.
  unfold R.v48125, N.v48125.
  unfold R.v6, N.v6.
  rewrite ?node_48124.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48126 (s : N.State) (i : N.Inputs) :
  R.v48126 (state s) (inputs i) = Zmod.unsigned (N.v48126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48126 s i)) at 1.
  unfold R.v48126, N.v48126.
  rewrite ?node_15692.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48127 (s : N.State) (i : N.Inputs) :
  R.v48127 (state s) (inputs i) = Zmod.unsigned (N.v48127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48127 s i)) at 1.
  unfold R.v48127, N.v48127.
  unfold R.v6, N.v6.
  rewrite ?node_15747.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48128 (s : N.State) (i : N.Inputs) :
  R.v48128 (state s) (inputs i) = Zmod.unsigned (N.v48128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48128 s i)) at 1.
  unfold R.v48128, N.v48128.
  rewrite ?node_48126.
  rewrite ?node_48127.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48129 (s : N.State) (i : N.Inputs) :
  R.v48129 (state s) (inputs i) = Zmod.unsigned (N.v48129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48129 s i)) at 1.
  unfold R.v48129, N.v48129.
  rewrite ?node_48125.
  rewrite ?node_48128.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48130 (s : N.State) (i : N.Inputs) :
  R.v48130 (state s) (inputs i) = Zmod.unsigned (N.v48130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48130 s i)) at 1.
  unfold R.v48130, N.v48130.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48131 (s : N.State) (i : N.Inputs) :
  R.v48131 (state s) (inputs i) = Zmod.unsigned (N.v48131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48131 s i)) at 1.
  unfold R.v48131, N.v48131.
  rewrite ?node_15699.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48132 (s : N.State) (i : N.Inputs) :
  R.v48132 (state s) (inputs i) = Zmod.unsigned (N.v48132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48132 s i)) at 1.
  unfold R.v48132, N.v48132.
  unfold R.v6, N.v6.
  rewrite ?node_15695.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48133 (s : N.State) (i : N.Inputs) :
  R.v48133 (state s) (inputs i) = Zmod.unsigned (N.v48133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48133 s i)) at 1.
  unfold R.v48133, N.v48133.
  unfold R.v6, N.v6.
  rewrite ?node_15692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48134 (s : N.State) (i : N.Inputs) :
  R.v48134 (state s) (inputs i) = Zmod.unsigned (N.v48134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48134 s i)) at 1.
  unfold R.v48134, N.v48134.
  rewrite ?node_48132.
  rewrite ?node_48133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48135 (s : N.State) (i : N.Inputs) :
  R.v48135 (state s) (inputs i) = Zmod.unsigned (N.v48135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48135 s i)) at 1.
  unfold R.v48135, N.v48135.
  unfold R.v16484, N.v16484.
  rewrite ?node_48134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48136 (s : N.State) (i : N.Inputs) :
  R.v48136 (state s) (inputs i) = Zmod.unsigned (N.v48136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48136 s i)) at 1.
  unfold R.v48136, N.v48136.
  rewrite ?node_48131.
  rewrite ?node_48135.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48137 (s : N.State) (i : N.Inputs) :
  R.v48137 (state s) (inputs i) = Zmod.unsigned (N.v48137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48137 s i)) at 1.
  unfold R.v48137, N.v48137.
  unfold R.v6, N.v6.
  rewrite ?node_48136.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48138 (s : N.State) (i : N.Inputs) :
  R.v48138 (state s) (inputs i) = Zmod.unsigned (N.v48138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48138 s i)) at 1.
  unfold R.v48138, N.v48138.
  rewrite ?node_15700.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48139 (s : N.State) (i : N.Inputs) :
  R.v48139 (state s) (inputs i) = Zmod.unsigned (N.v48139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48139 s i)) at 1.
  unfold R.v48139, N.v48139.
  unfold R.v6, N.v6.
  rewrite ?node_15757.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48140 (s : N.State) (i : N.Inputs) :
  R.v48140 (state s) (inputs i) = Zmod.unsigned (N.v48140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48140 s i)) at 1.
  unfold R.v48140, N.v48140.
  rewrite ?node_48138.
  rewrite ?node_48139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48141 (s : N.State) (i : N.Inputs) :
  R.v48141 (state s) (inputs i) = Zmod.unsigned (N.v48141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48141 s i)) at 1.
  unfold R.v48141, N.v48141.
  rewrite ?node_48137.
  rewrite ?node_48140.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48142 (s : N.State) (i : N.Inputs) :
  R.v48142 (state s) (inputs i) = Zmod.unsigned (N.v48142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48142 s i)) at 1.
  unfold R.v48142, N.v48142.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48143 (s : N.State) (i : N.Inputs) :
  R.v48143 (state s) (inputs i) = Zmod.unsigned (N.v48143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48143 s i)) at 1.
  unfold R.v48143, N.v48143.
  unfold R.v6, N.v6.
  rewrite ?node_15704.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48144 (s : N.State) (i : N.Inputs) :
  R.v48144 (state s) (inputs i) = Zmod.unsigned (N.v48144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48144 s i)) at 1.
  unfold R.v48144, N.v48144.
  unfold R.v6, N.v6.
  rewrite ?node_15703.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48145 (s : N.State) (i : N.Inputs) :
  R.v48145 (state s) (inputs i) = Zmod.unsigned (N.v48145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48145 s i)) at 1.
  unfold R.v48145, N.v48145.
  rewrite ?node_48143.
  rewrite ?node_48144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48146 (s : N.State) (i : N.Inputs) :
  R.v48146 (state s) (inputs i) = Zmod.unsigned (N.v48146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48146 s i)) at 1.
  unfold R.v48146, N.v48146.
  unfold R.v16463, N.v16463.
  rewrite ?node_48145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48147 (s : N.State) (i : N.Inputs) :
  R.v48147 (state s) (inputs i) = Zmod.unsigned (N.v48147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48147 s i)) at 1.
  unfold R.v48147, N.v48147.
  rewrite ?node_15705.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48148 (s : N.State) (i : N.Inputs) :
  R.v48148 (state s) (inputs i) = Zmod.unsigned (N.v48148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48148 s i)) at 1.
  unfold R.v48148, N.v48148.
  unfold R.v6, N.v6.
  rewrite ?node_15759.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48149 (s : N.State) (i : N.Inputs) :
  R.v48149 (state s) (inputs i) = Zmod.unsigned (N.v48149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48149 s i)) at 1.
  unfold R.v48149, N.v48149.
  rewrite ?node_48147.
  rewrite ?node_48148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48150 (s : N.State) (i : N.Inputs) :
  R.v48150 (state s) (inputs i) = Zmod.unsigned (N.v48150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48150 s i)) at 1.
  unfold R.v48150, N.v48150.
  rewrite ?node_48146.
  rewrite ?node_48149.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48151 (s : N.State) (i : N.Inputs) :
  R.v48151 (state s) (inputs i) = Zmod.unsigned (N.v48151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48151 s i)) at 1.
  unfold R.v48151, N.v48151.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48152 (s : N.State) (i : N.Inputs) :
  R.v48152 (state s) (inputs i) = Zmod.unsigned (N.v48152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48152 s i)) at 1.
  unfold R.v48152, N.v48152.
  rewrite ?node_15747.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48153 (s : N.State) (i : N.Inputs) :
  R.v48153 (state s) (inputs i) = Zmod.unsigned (N.v48153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48153 s i)) at 1.
  unfold R.v48153, N.v48153.
  rewrite ?node_15743.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48154 (s : N.State) (i : N.Inputs) :
  R.v48154 (state s) (inputs i) = Zmod.unsigned (N.v48154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48154 s i)) at 1.
  unfold R.v48154, N.v48154.
  unfold R.v16463, N.v16463.
  rewrite !state_r2206_nr_5F2229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2206_nr_5F2229 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48155 (s : N.State) (i : N.Inputs) :
  R.v48155 (state s) (inputs i) = Zmod.unsigned (N.v48155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48155 s i)) at 1.
  unfold R.v48155, N.v48155.
  unfold R.v6, N.v6.
  rewrite ?node_15738.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48156 (s : N.State) (i : N.Inputs) :
  R.v48156 (state s) (inputs i) = Zmod.unsigned (N.v48156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48156 s i)) at 1.
  unfold R.v48156, N.v48156.
  unfold R.v6, N.v6.
  rewrite ?node_15731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48157 (s : N.State) (i : N.Inputs) :
  R.v48157 (state s) (inputs i) = Zmod.unsigned (N.v48157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48157 s i)) at 1.
  unfold R.v48157, N.v48157.
  rewrite ?node_48155.
  rewrite ?node_48156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48158 (s : N.State) (i : N.Inputs) :
  R.v48158 (state s) (inputs i) = Zmod.unsigned (N.v48158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48158 s i)) at 1.
  unfold R.v48158, N.v48158.
  unfold R.v16484, N.v16484.
  rewrite ?node_48157.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48159 (s : N.State) (i : N.Inputs) :
  R.v48159 (state s) (inputs i) = Zmod.unsigned (N.v48159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48159 s i)) at 1.
  unfold R.v48159, N.v48159.
  rewrite ?node_48152.
  rewrite ?node_48153.
  rewrite ?node_48154.
  rewrite ?node_48158.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48160 (s : N.State) (i : N.Inputs) :
  R.v48160 (state s) (inputs i) = Zmod.unsigned (N.v48160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48160 s i)) at 1.
  unfold R.v48160, N.v48160.
  unfold R.v6, N.v6.
  rewrite ?node_48159.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48161 (s : N.State) (i : N.Inputs) :
  R.v48161 (state s) (inputs i) = Zmod.unsigned (N.v48161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48161 s i)) at 1.
  unfold R.v48161, N.v48161.
  rewrite ?node_15748.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48162 (s : N.State) (i : N.Inputs) :
  R.v48162 (state s) (inputs i) = Zmod.unsigned (N.v48162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48162 s i)) at 1.
  unfold R.v48162, N.v48162.
  unfold R.v6, N.v6.
  rewrite ?node_15796.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48163 (s : N.State) (i : N.Inputs) :
  R.v48163 (state s) (inputs i) = Zmod.unsigned (N.v48163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48163 s i)) at 1.
  unfold R.v48163, N.v48163.
  unfold R.v6, N.v6.
  rewrite ?node_15804.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48164 (s : N.State) (i : N.Inputs) :
  R.v48164 (state s) (inputs i) = Zmod.unsigned (N.v48164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48164 s i)) at 1.
  unfold R.v48164, N.v48164.
  rewrite ?node_48161.
  rewrite ?node_48162.
  rewrite ?node_48163.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48165 (s : N.State) (i : N.Inputs) :
  R.v48165 (state s) (inputs i) = Zmod.unsigned (N.v48165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48165 s i)) at 1.
  unfold R.v48165, N.v48165.
  rewrite ?node_48160.
  rewrite ?node_48164.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48166 (s : N.State) (i : N.Inputs) :
  R.v48166 (state s) (inputs i) = Zmod.unsigned (N.v48166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48166 s i)) at 1.
  unfold R.v48166, N.v48166.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48167 (s : N.State) (i : N.Inputs) :
  R.v48167 (state s) (inputs i) = Zmod.unsigned (N.v48167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48167 s i)) at 1.
  unfold R.v48167, N.v48167.
  unfold R.v16463, N.v16463.
  rewrite !state_r2206_nr_5F2229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2206_nr_5F2229 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48168 (s : N.State) (i : N.Inputs) :
  R.v48168 (state s) (inputs i) = Zmod.unsigned (N.v48168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48168 s i)) at 1.
  unfold R.v48168, N.v48168.
  unfold R.v6, N.v6.
  rewrite ?node_15738.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48169 (s : N.State) (i : N.Inputs) :
  R.v48169 (state s) (inputs i) = Zmod.unsigned (N.v48169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48169 s i)) at 1.
  unfold R.v48169, N.v48169.
  unfold R.v6, N.v6.
  rewrite ?node_15731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48170 (s : N.State) (i : N.Inputs) :
  R.v48170 (state s) (inputs i) = Zmod.unsigned (N.v48170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48170 s i)) at 1.
  unfold R.v48170, N.v48170.
  rewrite ?node_48168.
  rewrite ?node_48169.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48171 (s : N.State) (i : N.Inputs) :
  R.v48171 (state s) (inputs i) = Zmod.unsigned (N.v48171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48171 s i)) at 1.
  unfold R.v48171, N.v48171.
  unfold R.v16484, N.v16484.
  rewrite ?node_48170.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48172 (s : N.State) (i : N.Inputs) :
  R.v48172 (state s) (inputs i) = Zmod.unsigned (N.v48172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48172 s i)) at 1.
  unfold R.v48172, N.v48172.
  rewrite ?node_48167.
  rewrite ?node_48171.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48173 (s : N.State) (i : N.Inputs) :
  R.v48173 (state s) (inputs i) = Zmod.unsigned (N.v48173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48173 s i)) at 1.
  unfold R.v48173, N.v48173.
  unfold R.v6, N.v6.
  rewrite ?node_48172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48174 (s : N.State) (i : N.Inputs) :
  R.v48174 (state s) (inputs i) = Zmod.unsigned (N.v48174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48174 s i)) at 1.
  unfold R.v48174, N.v48174.
  rewrite ?node_15740.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48175 (s : N.State) (i : N.Inputs) :
  R.v48175 (state s) (inputs i) = Zmod.unsigned (N.v48175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48175 s i)) at 1.
  unfold R.v48175, N.v48175.
  unfold R.v6, N.v6.
  rewrite ?node_15796.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48176 (s : N.State) (i : N.Inputs) :
  R.v48176 (state s) (inputs i) = Zmod.unsigned (N.v48176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48176 s i)) at 1.
  unfold R.v48176, N.v48176.
  rewrite ?node_48174.
  rewrite ?node_48175.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48177 (s : N.State) (i : N.Inputs) :
  R.v48177 (state s) (inputs i) = Zmod.unsigned (N.v48177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48177 s i)) at 1.
  unfold R.v48177, N.v48177.
  rewrite ?node_48173.
  rewrite ?node_48176.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48178 (s : N.State) (i : N.Inputs) :
  R.v48178 (state s) (inputs i) = Zmod.unsigned (N.v48178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48178 s i)) at 1.
  unfold R.v48178, N.v48178.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48179 (s : N.State) (i : N.Inputs) :
  R.v48179 (state s) (inputs i) = Zmod.unsigned (N.v48179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48179 s i)) at 1.
  unfold R.v48179, N.v48179.
  rewrite ?node_15747.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48180 (s : N.State) (i : N.Inputs) :
  R.v48180 (state s) (inputs i) = Zmod.unsigned (N.v48180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48180 s i)) at 1.
  unfold R.v48180, N.v48180.
  unfold R.v6, N.v6.
  rewrite ?node_15743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48181 (s : N.State) (i : N.Inputs) :
  R.v48181 (state s) (inputs i) = Zmod.unsigned (N.v48181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48181 s i)) at 1.
  unfold R.v48181, N.v48181.
  unfold R.v6, N.v6.
  rewrite ?node_15740.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48182 (s : N.State) (i : N.Inputs) :
  R.v48182 (state s) (inputs i) = Zmod.unsigned (N.v48182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48182 s i)) at 1.
  unfold R.v48182, N.v48182.
  rewrite ?node_48180.
  rewrite ?node_48181.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48183 (s : N.State) (i : N.Inputs) :
  R.v48183 (state s) (inputs i) = Zmod.unsigned (N.v48183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48183 s i)) at 1.
  unfold R.v48183, N.v48183.
  unfold R.v16484, N.v16484.
  rewrite ?node_48182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48184 (s : N.State) (i : N.Inputs) :
  R.v48184 (state s) (inputs i) = Zmod.unsigned (N.v48184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48184 s i)) at 1.
  unfold R.v48184, N.v48184.
  rewrite ?node_48179.
  rewrite ?node_48183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48185 (s : N.State) (i : N.Inputs) :
  R.v48185 (state s) (inputs i) = Zmod.unsigned (N.v48185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48185 s i)) at 1.
  unfold R.v48185, N.v48185.
  unfold R.v6, N.v6.
  rewrite ?node_48184.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48186 (s : N.State) (i : N.Inputs) :
  R.v48186 (state s) (inputs i) = Zmod.unsigned (N.v48186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48186 s i)) at 1.
  unfold R.v48186, N.v48186.
  rewrite ?node_15748.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48187 (s : N.State) (i : N.Inputs) :
  R.v48187 (state s) (inputs i) = Zmod.unsigned (N.v48187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48187 s i)) at 1.
  unfold R.v48187, N.v48187.
  unfold R.v6, N.v6.
  rewrite ?node_15804.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48188 (s : N.State) (i : N.Inputs) :
  R.v48188 (state s) (inputs i) = Zmod.unsigned (N.v48188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48188 s i)) at 1.
  unfold R.v48188, N.v48188.
  rewrite ?node_48186.
  rewrite ?node_48187.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48189 (s : N.State) (i : N.Inputs) :
  R.v48189 (state s) (inputs i) = Zmod.unsigned (N.v48189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48189 s i)) at 1.
  unfold R.v48189, N.v48189.
  rewrite ?node_48185.
  rewrite ?node_48188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48190 (s : N.State) (i : N.Inputs) :
  R.v48190 (state s) (inputs i) = Zmod.unsigned (N.v48190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48190 s i)) at 1.
  unfold R.v48190, N.v48190.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48191 (s : N.State) (i : N.Inputs) :
  R.v48191 (state s) (inputs i) = Zmod.unsigned (N.v48191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48191 s i)) at 1.
  unfold R.v48191, N.v48191.
  unfold R.v6, N.v6.
  rewrite ?node_15752.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48192 (s : N.State) (i : N.Inputs) :
  R.v48192 (state s) (inputs i) = Zmod.unsigned (N.v48192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48192 s i)) at 1.
  unfold R.v48192, N.v48192.
  unfold R.v6, N.v6.
  rewrite ?node_15751.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48193 (s : N.State) (i : N.Inputs) :
  R.v48193 (state s) (inputs i) = Zmod.unsigned (N.v48193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48193 s i)) at 1.
  unfold R.v48193, N.v48193.
  rewrite ?node_48191.
  rewrite ?node_48192.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48194 (s : N.State) (i : N.Inputs) :
  R.v48194 (state s) (inputs i) = Zmod.unsigned (N.v48194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48194 s i)) at 1.
  unfold R.v48194, N.v48194.
  unfold R.v16463, N.v16463.
  rewrite ?node_48193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48195 (s : N.State) (i : N.Inputs) :
  R.v48195 (state s) (inputs i) = Zmod.unsigned (N.v48195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48195 s i)) at 1.
  unfold R.v48195, N.v48195.
  rewrite ?node_15753.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48196 (s : N.State) (i : N.Inputs) :
  R.v48196 (state s) (inputs i) = Zmod.unsigned (N.v48196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48196 s i)) at 1.
  unfold R.v48196, N.v48196.
  unfold R.v6, N.v6.
  rewrite ?node_15806.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48197 (s : N.State) (i : N.Inputs) :
  R.v48197 (state s) (inputs i) = Zmod.unsigned (N.v48197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48197 s i)) at 1.
  unfold R.v48197, N.v48197.
  rewrite ?node_48195.
  rewrite ?node_48196.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48198 (s : N.State) (i : N.Inputs) :
  R.v48198 (state s) (inputs i) = Zmod.unsigned (N.v48198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48198 s i)) at 1.
  unfold R.v48198, N.v48198.
  rewrite ?node_48194.
  rewrite ?node_48197.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48199 (s : N.State) (i : N.Inputs) :
  R.v48199 (state s) (inputs i) = Zmod.unsigned (N.v48199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48199 s i)) at 1.
  unfold R.v48199, N.v48199.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48200 (s : N.State) (i : N.Inputs) :
  R.v48200 (state s) (inputs i) = Zmod.unsigned (N.v48200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48200 s i)) at 1.
  unfold R.v48200, N.v48200.
  rewrite ?node_15796.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48201 (s : N.State) (i : N.Inputs) :
  R.v48201 (state s) (inputs i) = Zmod.unsigned (N.v48201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48201 s i)) at 1.
  unfold R.v48201, N.v48201.
  rewrite ?node_15792.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48202 (s : N.State) (i : N.Inputs) :
  R.v48202 (state s) (inputs i) = Zmod.unsigned (N.v48202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48202 s i)) at 1.
  unfold R.v48202, N.v48202.
  unfold R.v16463, N.v16463.
  rewrite !state_r2214_nr_5F2238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2214_nr_5F2238 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48203 (s : N.State) (i : N.Inputs) :
  R.v48203 (state s) (inputs i) = Zmod.unsigned (N.v48203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48203 s i)) at 1.
  unfold R.v48203, N.v48203.
  unfold R.v6, N.v6.
  rewrite ?node_15787.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48204 (s : N.State) (i : N.Inputs) :
  R.v48204 (state s) (inputs i) = Zmod.unsigned (N.v48204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48204 s i)) at 1.
  unfold R.v48204, N.v48204.
  unfold R.v6, N.v6.
  rewrite ?node_15780.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48205 (s : N.State) (i : N.Inputs) :
  R.v48205 (state s) (inputs i) = Zmod.unsigned (N.v48205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48205 s i)) at 1.
  unfold R.v48205, N.v48205.
  rewrite ?node_48203.
  rewrite ?node_48204.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48206 (s : N.State) (i : N.Inputs) :
  R.v48206 (state s) (inputs i) = Zmod.unsigned (N.v48206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48206 s i)) at 1.
  unfold R.v48206, N.v48206.
  unfold R.v16484, N.v16484.
  rewrite ?node_48205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48207 (s : N.State) (i : N.Inputs) :
  R.v48207 (state s) (inputs i) = Zmod.unsigned (N.v48207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48207 s i)) at 1.
  unfold R.v48207, N.v48207.
  rewrite ?node_48200.
  rewrite ?node_48201.
  rewrite ?node_48202.
  rewrite ?node_48206.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48208 (s : N.State) (i : N.Inputs) :
  R.v48208 (state s) (inputs i) = Zmod.unsigned (N.v48208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48208 s i)) at 1.
  unfold R.v48208, N.v48208.
  unfold R.v6, N.v6.
  rewrite ?node_48207.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48209 (s : N.State) (i : N.Inputs) :
  R.v48209 (state s) (inputs i) = Zmod.unsigned (N.v48209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48209 s i)) at 1.
  unfold R.v48209, N.v48209.
  rewrite ?node_15797.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48210 (s : N.State) (i : N.Inputs) :
  R.v48210 (state s) (inputs i) = Zmod.unsigned (N.v48210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48210 s i)) at 1.
  unfold R.v48210, N.v48210.
  unfold R.v6, N.v6.
  rewrite ?node_15845.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48211 (s : N.State) (i : N.Inputs) :
  R.v48211 (state s) (inputs i) = Zmod.unsigned (N.v48211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48211 s i)) at 1.
  unfold R.v48211, N.v48211.
  unfold R.v6, N.v6.
  rewrite ?node_15849.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48212 (s : N.State) (i : N.Inputs) :
  R.v48212 (state s) (inputs i) = Zmod.unsigned (N.v48212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48212 s i)) at 1.
  unfold R.v48212, N.v48212.
  rewrite ?node_48209.
  rewrite ?node_48210.
  rewrite ?node_48211.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48213 (s : N.State) (i : N.Inputs) :
  R.v48213 (state s) (inputs i) = Zmod.unsigned (N.v48213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48213 s i)) at 1.
  unfold R.v48213, N.v48213.
  rewrite ?node_48208.
  rewrite ?node_48212.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48214 (s : N.State) (i : N.Inputs) :
  R.v48214 (state s) (inputs i) = Zmod.unsigned (N.v48214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48214 s i)) at 1.
  unfold R.v48214, N.v48214.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48215 (s : N.State) (i : N.Inputs) :
  R.v48215 (state s) (inputs i) = Zmod.unsigned (N.v48215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48215 s i)) at 1.
  unfold R.v48215, N.v48215.
  unfold R.v16463, N.v16463.
  rewrite !state_r2214_nr_5F2238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2214_nr_5F2238 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48216 (s : N.State) (i : N.Inputs) :
  R.v48216 (state s) (inputs i) = Zmod.unsigned (N.v48216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48216 s i)) at 1.
  unfold R.v48216, N.v48216.
  unfold R.v6, N.v6.
  rewrite ?node_15787.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48217 (s : N.State) (i : N.Inputs) :
  R.v48217 (state s) (inputs i) = Zmod.unsigned (N.v48217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48217 s i)) at 1.
  unfold R.v48217, N.v48217.
  unfold R.v6, N.v6.
  rewrite ?node_15780.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48218 (s : N.State) (i : N.Inputs) :
  R.v48218 (state s) (inputs i) = Zmod.unsigned (N.v48218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48218 s i)) at 1.
  unfold R.v48218, N.v48218.
  rewrite ?node_48216.
  rewrite ?node_48217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48219 (s : N.State) (i : N.Inputs) :
  R.v48219 (state s) (inputs i) = Zmod.unsigned (N.v48219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48219 s i)) at 1.
  unfold R.v48219, N.v48219.
  unfold R.v16484, N.v16484.
  rewrite ?node_48218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48220 (s : N.State) (i : N.Inputs) :
  R.v48220 (state s) (inputs i) = Zmod.unsigned (N.v48220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48220 s i)) at 1.
  unfold R.v48220, N.v48220.
  rewrite ?node_48215.
  rewrite ?node_48219.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48221 (s : N.State) (i : N.Inputs) :
  R.v48221 (state s) (inputs i) = Zmod.unsigned (N.v48221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48221 s i)) at 1.
  unfold R.v48221, N.v48221.
  unfold R.v6, N.v6.
  rewrite ?node_48220.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48222 (s : N.State) (i : N.Inputs) :
  R.v48222 (state s) (inputs i) = Zmod.unsigned (N.v48222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48222 s i)) at 1.
  unfold R.v48222, N.v48222.
  rewrite ?node_15789.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48223 (s : N.State) (i : N.Inputs) :
  R.v48223 (state s) (inputs i) = Zmod.unsigned (N.v48223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48223 s i)) at 1.
  unfold R.v48223, N.v48223.
  unfold R.v6, N.v6.
  rewrite ?node_15845.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48224 (s : N.State) (i : N.Inputs) :
  R.v48224 (state s) (inputs i) = Zmod.unsigned (N.v48224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48224 s i)) at 1.
  unfold R.v48224, N.v48224.
  rewrite ?node_48222.
  rewrite ?node_48223.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48225 (s : N.State) (i : N.Inputs) :
  R.v48225 (state s) (inputs i) = Zmod.unsigned (N.v48225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48225 s i)) at 1.
  unfold R.v48225, N.v48225.
  rewrite ?node_48221.
  rewrite ?node_48224.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48226 (s : N.State) (i : N.Inputs) :
  R.v48226 (state s) (inputs i) = Zmod.unsigned (N.v48226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48226 s i)) at 1.
  unfold R.v48226, N.v48226.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48227 (s : N.State) (i : N.Inputs) :
  R.v48227 (state s) (inputs i) = Zmod.unsigned (N.v48227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48227 s i)) at 1.
  unfold R.v48227, N.v48227.
  rewrite ?node_15796.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48228 (s : N.State) (i : N.Inputs) :
  R.v48228 (state s) (inputs i) = Zmod.unsigned (N.v48228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48228 s i)) at 1.
  unfold R.v48228, N.v48228.
  unfold R.v6, N.v6.
  rewrite ?node_15792.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48229 (s : N.State) (i : N.Inputs) :
  R.v48229 (state s) (inputs i) = Zmod.unsigned (N.v48229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48229 s i)) at 1.
  unfold R.v48229, N.v48229.
  unfold R.v6, N.v6.
  rewrite ?node_15789.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48230 (s : N.State) (i : N.Inputs) :
  R.v48230 (state s) (inputs i) = Zmod.unsigned (N.v48230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48230 s i)) at 1.
  unfold R.v48230, N.v48230.
  rewrite ?node_48228.
  rewrite ?node_48229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48231 (s : N.State) (i : N.Inputs) :
  R.v48231 (state s) (inputs i) = Zmod.unsigned (N.v48231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48231 s i)) at 1.
  unfold R.v48231, N.v48231.
  unfold R.v16484, N.v16484.
  rewrite ?node_48230.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48232 (s : N.State) (i : N.Inputs) :
  R.v48232 (state s) (inputs i) = Zmod.unsigned (N.v48232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48232 s i)) at 1.
  unfold R.v48232, N.v48232.
  rewrite ?node_48227.
  rewrite ?node_48231.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48233 (s : N.State) (i : N.Inputs) :
  R.v48233 (state s) (inputs i) = Zmod.unsigned (N.v48233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48233 s i)) at 1.
  unfold R.v48233, N.v48233.
  unfold R.v6, N.v6.
  rewrite ?node_48232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48234 (s : N.State) (i : N.Inputs) :
  R.v48234 (state s) (inputs i) = Zmod.unsigned (N.v48234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48234 s i)) at 1.
  unfold R.v48234, N.v48234.
  rewrite ?node_15797.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48235 (s : N.State) (i : N.Inputs) :
  R.v48235 (state s) (inputs i) = Zmod.unsigned (N.v48235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48235 s i)) at 1.
  unfold R.v48235, N.v48235.
  unfold R.v6, N.v6.
  rewrite ?node_15849.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48236 (s : N.State) (i : N.Inputs) :
  R.v48236 (state s) (inputs i) = Zmod.unsigned (N.v48236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48236 s i)) at 1.
  unfold R.v48236, N.v48236.
  rewrite ?node_48234.
  rewrite ?node_48235.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48237 (s : N.State) (i : N.Inputs) :
  R.v48237 (state s) (inputs i) = Zmod.unsigned (N.v48237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48237 s i)) at 1.
  unfold R.v48237, N.v48237.
  rewrite ?node_48233.
  rewrite ?node_48236.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48238 (s : N.State) (i : N.Inputs) :
  R.v48238 (state s) (inputs i) = Zmod.unsigned (N.v48238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48238 s i)) at 1.
  unfold R.v48238, N.v48238.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48239 (s : N.State) (i : N.Inputs) :
  R.v48239 (state s) (inputs i) = Zmod.unsigned (N.v48239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48239 s i)) at 1.
  unfold R.v48239, N.v48239.
  rewrite ?node_15845.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48240 (s : N.State) (i : N.Inputs) :
  R.v48240 (state s) (inputs i) = Zmod.unsigned (N.v48240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48240 s i)) at 1.
  unfold R.v48240, N.v48240.
  rewrite ?node_15841.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48241 (s : N.State) (i : N.Inputs) :
  R.v48241 (state s) (inputs i) = Zmod.unsigned (N.v48241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48241 s i)) at 1.
  unfold R.v48241, N.v48241.
  rewrite ?node_15837.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48242 (s : N.State) (i : N.Inputs) :
  R.v48242 (state s) (inputs i) = Zmod.unsigned (N.v48242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48242 s i)) at 1.
  unfold R.v48242, N.v48242.
  unfold R.v6, N.v6.
  rewrite ?node_15833.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48243 (s : N.State) (i : N.Inputs) :
  R.v48243 (state s) (inputs i) = Zmod.unsigned (N.v48243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48243 s i)) at 1.
  unfold R.v48243, N.v48243.
  unfold R.v6, N.v6.
  rewrite ?node_15826.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48244 (s : N.State) (i : N.Inputs) :
  R.v48244 (state s) (inputs i) = Zmod.unsigned (N.v48244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48244 s i)) at 1.
  unfold R.v48244, N.v48244.
  rewrite ?node_48242.
  rewrite ?node_48243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48245 (s : N.State) (i : N.Inputs) :
  R.v48245 (state s) (inputs i) = Zmod.unsigned (N.v48245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48245 s i)) at 1.
  unfold R.v48245, N.v48245.
  unfold R.v16484, N.v16484.
  rewrite ?node_48244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48246 (s : N.State) (i : N.Inputs) :
  R.v48246 (state s) (inputs i) = Zmod.unsigned (N.v48246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48246 s i)) at 1.
  unfold R.v48246, N.v48246.
  rewrite ?node_48239.
  rewrite ?node_48240.
  rewrite ?node_48241.
  rewrite ?node_48245.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48247 (s : N.State) (i : N.Inputs) :
  R.v48247 (state s) (inputs i) = Zmod.unsigned (N.v48247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48247 s i)) at 1.
  unfold R.v48247, N.v48247.
  unfold R.v6, N.v6.
  rewrite ?node_48246.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48248 (s : N.State) (i : N.Inputs) :
  R.v48248 (state s) (inputs i) = Zmod.unsigned (N.v48248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48248 s i)) at 1.
  unfold R.v48248, N.v48248.
  rewrite ?node_15846.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48249 (s : N.State) (i : N.Inputs) :
  R.v48249 (state s) (inputs i) = Zmod.unsigned (N.v48249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48249 s i)) at 1.
  unfold R.v48249, N.v48249.
  unfold R.v6, N.v6.
  rewrite ?node_15889.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48250 (s : N.State) (i : N.Inputs) :
  R.v48250 (state s) (inputs i) = Zmod.unsigned (N.v48250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48250 s i)) at 1.
  unfold R.v48250, N.v48250.
  unfold R.v6, N.v6.
  rewrite ?node_15893.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48251 (s : N.State) (i : N.Inputs) :
  R.v48251 (state s) (inputs i) = Zmod.unsigned (N.v48251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48251 s i)) at 1.
  unfold R.v48251, N.v48251.
  rewrite ?node_48248.
  rewrite ?node_48249.
  rewrite ?node_48250.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48252 (s : N.State) (i : N.Inputs) :
  R.v48252 (state s) (inputs i) = Zmod.unsigned (N.v48252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48252 s i)) at 1.
  unfold R.v48252, N.v48252.
  rewrite ?node_48247.
  rewrite ?node_48251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48253 (s : N.State) (i : N.Inputs) :
  R.v48253 (state s) (inputs i) = Zmod.unsigned (N.v48253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48253 s i)) at 1.
  unfold R.v48253, N.v48253.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48254 (s : N.State) (i : N.Inputs) :
  R.v48254 (state s) (inputs i) = Zmod.unsigned (N.v48254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48254 s i)) at 1.
  unfold R.v48254, N.v48254.
  rewrite ?node_15837.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48255 (s : N.State) (i : N.Inputs) :
  R.v48255 (state s) (inputs i) = Zmod.unsigned (N.v48255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48255 s i)) at 1.
  unfold R.v48255, N.v48255.
  unfold R.v6, N.v6.
  rewrite ?node_15833.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48256 (s : N.State) (i : N.Inputs) :
  R.v48256 (state s) (inputs i) = Zmod.unsigned (N.v48256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48256 s i)) at 1.
  unfold R.v48256, N.v48256.
  unfold R.v6, N.v6.
  rewrite ?node_15826.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48257 (s : N.State) (i : N.Inputs) :
  R.v48257 (state s) (inputs i) = Zmod.unsigned (N.v48257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48257 s i)) at 1.
  unfold R.v48257, N.v48257.
  rewrite ?node_48255.
  rewrite ?node_48256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48258 (s : N.State) (i : N.Inputs) :
  R.v48258 (state s) (inputs i) = Zmod.unsigned (N.v48258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48258 s i)) at 1.
  unfold R.v48258, N.v48258.
  unfold R.v16484, N.v16484.
  rewrite ?node_48257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48259 (s : N.State) (i : N.Inputs) :
  R.v48259 (state s) (inputs i) = Zmod.unsigned (N.v48259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48259 s i)) at 1.
  unfold R.v48259, N.v48259.
  rewrite ?node_48254.
  rewrite ?node_48258.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48260 (s : N.State) (i : N.Inputs) :
  R.v48260 (state s) (inputs i) = Zmod.unsigned (N.v48260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48260 s i)) at 1.
  unfold R.v48260, N.v48260.
  unfold R.v6, N.v6.
  rewrite ?node_48259.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48261 (s : N.State) (i : N.Inputs) :
  R.v48261 (state s) (inputs i) = Zmod.unsigned (N.v48261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48261 s i)) at 1.
  unfold R.v48261, N.v48261.
  rewrite ?node_15838.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48262 (s : N.State) (i : N.Inputs) :
  R.v48262 (state s) (inputs i) = Zmod.unsigned (N.v48262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48262 s i)) at 1.
  unfold R.v48262, N.v48262.
  unfold R.v6, N.v6.
  rewrite ?node_15889.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48263 (s : N.State) (i : N.Inputs) :
  R.v48263 (state s) (inputs i) = Zmod.unsigned (N.v48263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48263 s i)) at 1.
  unfold R.v48263, N.v48263.
  rewrite ?node_48261.
  rewrite ?node_48262.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48264 (s : N.State) (i : N.Inputs) :
  R.v48264 (state s) (inputs i) = Zmod.unsigned (N.v48264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48264 s i)) at 1.
  unfold R.v48264, N.v48264.
  rewrite ?node_48260.
  rewrite ?node_48263.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48265 (s : N.State) (i : N.Inputs) :
  R.v48265 (state s) (inputs i) = Zmod.unsigned (N.v48265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48265 s i)) at 1.
  unfold R.v48265, N.v48265.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48266 (s : N.State) (i : N.Inputs) :
  R.v48266 (state s) (inputs i) = Zmod.unsigned (N.v48266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48266 s i)) at 1.
  unfold R.v48266, N.v48266.
  rewrite ?node_15845.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48267 (s : N.State) (i : N.Inputs) :
  R.v48267 (state s) (inputs i) = Zmod.unsigned (N.v48267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48267 s i)) at 1.
  unfold R.v48267, N.v48267.
  unfold R.v6, N.v6.
  rewrite ?node_15841.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48268 (s : N.State) (i : N.Inputs) :
  R.v48268 (state s) (inputs i) = Zmod.unsigned (N.v48268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48268 s i)) at 1.
  unfold R.v48268, N.v48268.
  unfold R.v6, N.v6.
  rewrite ?node_15838.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48269 (s : N.State) (i : N.Inputs) :
  R.v48269 (state s) (inputs i) = Zmod.unsigned (N.v48269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48269 s i)) at 1.
  unfold R.v48269, N.v48269.
  rewrite ?node_48267.
  rewrite ?node_48268.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48270 (s : N.State) (i : N.Inputs) :
  R.v48270 (state s) (inputs i) = Zmod.unsigned (N.v48270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48270 s i)) at 1.
  unfold R.v48270, N.v48270.
  unfold R.v16484, N.v16484.
  rewrite ?node_48269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48271 (s : N.State) (i : N.Inputs) :
  R.v48271 (state s) (inputs i) = Zmod.unsigned (N.v48271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48271 s i)) at 1.
  unfold R.v48271, N.v48271.
  rewrite ?node_48266.
  rewrite ?node_48270.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48272 (s : N.State) (i : N.Inputs) :
  R.v48272 (state s) (inputs i) = Zmod.unsigned (N.v48272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48272 s i)) at 1.
  unfold R.v48272, N.v48272.
  unfold R.v6, N.v6.
  rewrite ?node_48271.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48273 (s : N.State) (i : N.Inputs) :
  R.v48273 (state s) (inputs i) = Zmod.unsigned (N.v48273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48273 s i)) at 1.
  unfold R.v48273, N.v48273.
  rewrite ?node_15846.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48274 (s : N.State) (i : N.Inputs) :
  R.v48274 (state s) (inputs i) = Zmod.unsigned (N.v48274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48274 s i)) at 1.
  unfold R.v48274, N.v48274.
  unfold R.v6, N.v6.
  rewrite ?node_15893.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48275 (s : N.State) (i : N.Inputs) :
  R.v48275 (state s) (inputs i) = Zmod.unsigned (N.v48275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48275 s i)) at 1.
  unfold R.v48275, N.v48275.
  rewrite ?node_48273.
  rewrite ?node_48274.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48276 (s : N.State) (i : N.Inputs) :
  R.v48276 (state s) (inputs i) = Zmod.unsigned (N.v48276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48276 s i)) at 1.
  unfold R.v48276, N.v48276.
  rewrite ?node_48272.
  rewrite ?node_48275.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48277 (s : N.State) (i : N.Inputs) :
  R.v48277 (state s) (inputs i) = Zmod.unsigned (N.v48277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48277 s i)) at 1.
  unfold R.v48277, N.v48277.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48278 (s : N.State) (i : N.Inputs) :
  R.v48278 (state s) (inputs i) = Zmod.unsigned (N.v48278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48278 s i)) at 1.
  unfold R.v48278, N.v48278.
  rewrite ?node_15889.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48279 (s : N.State) (i : N.Inputs) :
  R.v48279 (state s) (inputs i) = Zmod.unsigned (N.v48279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48279 s i)) at 1.
  unfold R.v48279, N.v48279.
  rewrite ?node_15885.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48280 (s : N.State) (i : N.Inputs) :
  R.v48280 (state s) (inputs i) = Zmod.unsigned (N.v48280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48280 s i)) at 1.
  unfold R.v48280, N.v48280.
  rewrite ?node_15881.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48281 (s : N.State) (i : N.Inputs) :
  R.v48281 (state s) (inputs i) = Zmod.unsigned (N.v48281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48281 s i)) at 1.
  unfold R.v48281, N.v48281.
  unfold R.v6, N.v6.
  rewrite ?node_15877.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48282 (s : N.State) (i : N.Inputs) :
  R.v48282 (state s) (inputs i) = Zmod.unsigned (N.v48282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48282 s i)) at 1.
  unfold R.v48282, N.v48282.
  unfold R.v6, N.v6.
  rewrite ?node_15870.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48283 (s : N.State) (i : N.Inputs) :
  R.v48283 (state s) (inputs i) = Zmod.unsigned (N.v48283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48283 s i)) at 1.
  unfold R.v48283, N.v48283.
  rewrite ?node_48281.
  rewrite ?node_48282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48284 (s : N.State) (i : N.Inputs) :
  R.v48284 (state s) (inputs i) = Zmod.unsigned (N.v48284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48284 s i)) at 1.
  unfold R.v48284, N.v48284.
  unfold R.v16484, N.v16484.
  rewrite ?node_48283.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48285 (s : N.State) (i : N.Inputs) :
  R.v48285 (state s) (inputs i) = Zmod.unsigned (N.v48285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48285 s i)) at 1.
  unfold R.v48285, N.v48285.
  rewrite ?node_48278.
  rewrite ?node_48279.
  rewrite ?node_48280.
  rewrite ?node_48284.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48286 (s : N.State) (i : N.Inputs) :
  R.v48286 (state s) (inputs i) = Zmod.unsigned (N.v48286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48286 s i)) at 1.
  unfold R.v48286, N.v48286.
  unfold R.v6, N.v6.
  rewrite ?node_48285.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48287 (s : N.State) (i : N.Inputs) :
  R.v48287 (state s) (inputs i) = Zmod.unsigned (N.v48287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48287 s i)) at 1.
  unfold R.v48287, N.v48287.
  rewrite ?node_15890.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48288 (s : N.State) (i : N.Inputs) :
  R.v48288 (state s) (inputs i) = Zmod.unsigned (N.v48288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48288 s i)) at 1.
  unfold R.v48288, N.v48288.
  unfold R.v6, N.v6.
  rewrite ?node_15923.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48289 (s : N.State) (i : N.Inputs) :
  R.v48289 (state s) (inputs i) = Zmod.unsigned (N.v48289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48289 s i)) at 1.
  unfold R.v48289, N.v48289.
  unfold R.v6, N.v6.
  rewrite ?node_15931.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48290 (s : N.State) (i : N.Inputs) :
  R.v48290 (state s) (inputs i) = Zmod.unsigned (N.v48290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48290 s i)) at 1.
  unfold R.v48290, N.v48290.
  rewrite ?node_48287.
  rewrite ?node_48288.
  rewrite ?node_48289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48291 (s : N.State) (i : N.Inputs) :
  R.v48291 (state s) (inputs i) = Zmod.unsigned (N.v48291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48291 s i)) at 1.
  unfold R.v48291, N.v48291.
  rewrite ?node_48286.
  rewrite ?node_48290.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48292 (s : N.State) (i : N.Inputs) :
  R.v48292 (state s) (inputs i) = Zmod.unsigned (N.v48292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48292 s i)) at 1.
  unfold R.v48292, N.v48292.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48293 (s : N.State) (i : N.Inputs) :
  R.v48293 (state s) (inputs i) = Zmod.unsigned (N.v48293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48293 s i)) at 1.
  unfold R.v48293, N.v48293.
  rewrite ?node_15881.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48294 (s : N.State) (i : N.Inputs) :
  R.v48294 (state s) (inputs i) = Zmod.unsigned (N.v48294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48294 s i)) at 1.
  unfold R.v48294, N.v48294.
  unfold R.v6, N.v6.
  rewrite ?node_15877.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48295 (s : N.State) (i : N.Inputs) :
  R.v48295 (state s) (inputs i) = Zmod.unsigned (N.v48295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48295 s i)) at 1.
  unfold R.v48295, N.v48295.
  unfold R.v6, N.v6.
  rewrite ?node_15870.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48296 (s : N.State) (i : N.Inputs) :
  R.v48296 (state s) (inputs i) = Zmod.unsigned (N.v48296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48296 s i)) at 1.
  unfold R.v48296, N.v48296.
  rewrite ?node_48294.
  rewrite ?node_48295.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48297 (s : N.State) (i : N.Inputs) :
  R.v48297 (state s) (inputs i) = Zmod.unsigned (N.v48297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48297 s i)) at 1.
  unfold R.v48297, N.v48297.
  unfold R.v16484, N.v16484.
  rewrite ?node_48296.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48298 (s : N.State) (i : N.Inputs) :
  R.v48298 (state s) (inputs i) = Zmod.unsigned (N.v48298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48298 s i)) at 1.
  unfold R.v48298, N.v48298.
  rewrite ?node_48293.
  rewrite ?node_48297.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48299 (s : N.State) (i : N.Inputs) :
  R.v48299 (state s) (inputs i) = Zmod.unsigned (N.v48299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48299 s i)) at 1.
  unfold R.v48299, N.v48299.
  unfold R.v6, N.v6.
  rewrite ?node_48298.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48300 (s : N.State) (i : N.Inputs) :
  R.v48300 (state s) (inputs i) = Zmod.unsigned (N.v48300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48300 s i)) at 1.
  unfold R.v48300, N.v48300.
  rewrite ?node_15882.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48301 (s : N.State) (i : N.Inputs) :
  R.v48301 (state s) (inputs i) = Zmod.unsigned (N.v48301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48301 s i)) at 1.
  unfold R.v48301, N.v48301.
  unfold R.v6, N.v6.
  rewrite ?node_15923.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48302 (s : N.State) (i : N.Inputs) :
  R.v48302 (state s) (inputs i) = Zmod.unsigned (N.v48302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48302 s i)) at 1.
  unfold R.v48302, N.v48302.
  rewrite ?node_48300.
  rewrite ?node_48301.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48303 (s : N.State) (i : N.Inputs) :
  R.v48303 (state s) (inputs i) = Zmod.unsigned (N.v48303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48303 s i)) at 1.
  unfold R.v48303, N.v48303.
  rewrite ?node_48299.
  rewrite ?node_48302.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48304 (s : N.State) (i : N.Inputs) :
  R.v48304 (state s) (inputs i) = Zmod.unsigned (N.v48304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48304 s i)) at 1.
  unfold R.v48304, N.v48304.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48305 (s : N.State) (i : N.Inputs) :
  R.v48305 (state s) (inputs i) = Zmod.unsigned (N.v48305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48305 s i)) at 1.
  unfold R.v48305, N.v48305.
  rewrite ?node_15889.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48306 (s : N.State) (i : N.Inputs) :
  R.v48306 (state s) (inputs i) = Zmod.unsigned (N.v48306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48306 s i)) at 1.
  unfold R.v48306, N.v48306.
  unfold R.v6, N.v6.
  rewrite ?node_15885.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48307 (s : N.State) (i : N.Inputs) :
  R.v48307 (state s) (inputs i) = Zmod.unsigned (N.v48307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48307 s i)) at 1.
  unfold R.v48307, N.v48307.
  unfold R.v6, N.v6.
  rewrite ?node_15882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48308 (s : N.State) (i : N.Inputs) :
  R.v48308 (state s) (inputs i) = Zmod.unsigned (N.v48308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48308 s i)) at 1.
  unfold R.v48308, N.v48308.
  rewrite ?node_48306.
  rewrite ?node_48307.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48309 (s : N.State) (i : N.Inputs) :
  R.v48309 (state s) (inputs i) = Zmod.unsigned (N.v48309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48309 s i)) at 1.
  unfold R.v48309, N.v48309.
  unfold R.v16484, N.v16484.
  rewrite ?node_48308.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48310 (s : N.State) (i : N.Inputs) :
  R.v48310 (state s) (inputs i) = Zmod.unsigned (N.v48310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48310 s i)) at 1.
  unfold R.v48310, N.v48310.
  rewrite ?node_48305.
  rewrite ?node_48309.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48311 (s : N.State) (i : N.Inputs) :
  R.v48311 (state s) (inputs i) = Zmod.unsigned (N.v48311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48311 s i)) at 1.
  unfold R.v48311, N.v48311.
  unfold R.v6, N.v6.
  rewrite ?node_48310.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48312 (s : N.State) (i : N.Inputs) :
  R.v48312 (state s) (inputs i) = Zmod.unsigned (N.v48312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48312 s i)) at 1.
  unfold R.v48312, N.v48312.
  rewrite ?node_15890.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48313 (s : N.State) (i : N.Inputs) :
  R.v48313 (state s) (inputs i) = Zmod.unsigned (N.v48313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48313 s i)) at 1.
  unfold R.v48313, N.v48313.
  unfold R.v6, N.v6.
  rewrite ?node_15931.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48314 (s : N.State) (i : N.Inputs) :
  R.v48314 (state s) (inputs i) = Zmod.unsigned (N.v48314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48314 s i)) at 1.
  unfold R.v48314, N.v48314.
  rewrite ?node_48312.
  rewrite ?node_48313.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48315 (s : N.State) (i : N.Inputs) :
  R.v48315 (state s) (inputs i) = Zmod.unsigned (N.v48315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48315 s i)) at 1.
  unfold R.v48315, N.v48315.
  rewrite ?node_48311.
  rewrite ?node_48314.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48316 (s : N.State) (i : N.Inputs) :
  R.v48316 (state s) (inputs i) = Zmod.unsigned (N.v48316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48316 s i)) at 1.
  unfold R.v48316, N.v48316.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48317 (s : N.State) (i : N.Inputs) :
  R.v48317 (state s) (inputs i) = Zmod.unsigned (N.v48317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48317 s i)) at 1.
  unfold R.v48317, N.v48317.
  rewrite ?node_15923.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48318 (s : N.State) (i : N.Inputs) :
  R.v48318 (state s) (inputs i) = Zmod.unsigned (N.v48318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48318 s i)) at 1.
  unfold R.v48318, N.v48318.
  rewrite ?node_15919.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48319 (s : N.State) (i : N.Inputs) :
  R.v48319 (state s) (inputs i) = Zmod.unsigned (N.v48319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48319 s i)) at 1.
  unfold R.v48319, N.v48319.
  rewrite ?node_15915.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48320 (s : N.State) (i : N.Inputs) :
  R.v48320 (state s) (inputs i) = Zmod.unsigned (N.v48320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48320 s i)) at 1.
  unfold R.v48320, N.v48320.
  unfold R.v6, N.v6.
  rewrite ?node_15911.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48321 (s : N.State) (i : N.Inputs) :
  R.v48321 (state s) (inputs i) = Zmod.unsigned (N.v48321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48321 s i)) at 1.
  unfold R.v48321, N.v48321.
  unfold R.v6, N.v6.
  rewrite ?node_15909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48322 (s : N.State) (i : N.Inputs) :
  R.v48322 (state s) (inputs i) = Zmod.unsigned (N.v48322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48322 s i)) at 1.
  unfold R.v48322, N.v48322.
  rewrite ?node_48320.
  rewrite ?node_48321.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48323 (s : N.State) (i : N.Inputs) :
  R.v48323 (state s) (inputs i) = Zmod.unsigned (N.v48323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48323 s i)) at 1.
  unfold R.v48323, N.v48323.
  unfold R.v16484, N.v16484.
  rewrite ?node_48322.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48324 (s : N.State) (i : N.Inputs) :
  R.v48324 (state s) (inputs i) = Zmod.unsigned (N.v48324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48324 s i)) at 1.
  unfold R.v48324, N.v48324.
  rewrite ?node_48317.
  rewrite ?node_48318.
  rewrite ?node_48319.
  rewrite ?node_48323.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48325 (s : N.State) (i : N.Inputs) :
  R.v48325 (state s) (inputs i) = Zmod.unsigned (N.v48325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48325 s i)) at 1.
  unfold R.v48325, N.v48325.
  unfold R.v6, N.v6.
  rewrite ?node_48324.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48326 (s : N.State) (i : N.Inputs) :
  R.v48326 (state s) (inputs i) = Zmod.unsigned (N.v48326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48326 s i)) at 1.
  unfold R.v48326, N.v48326.
  rewrite ?node_15924.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48327 (s : N.State) (i : N.Inputs) :
  R.v48327 (state s) (inputs i) = Zmod.unsigned (N.v48327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48327 s i)) at 1.
  unfold R.v48327, N.v48327.
  unfold R.v6, N.v6.
  rewrite ?node_15960.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48328 (s : N.State) (i : N.Inputs) :
  R.v48328 (state s) (inputs i) = Zmod.unsigned (N.v48328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48328 s i)) at 1.
  unfold R.v48328, N.v48328.
  unfold R.v6, N.v6.
  rewrite ?node_15964.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48329 (s : N.State) (i : N.Inputs) :
  R.v48329 (state s) (inputs i) = Zmod.unsigned (N.v48329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48329 s i)) at 1.
  unfold R.v48329, N.v48329.
  rewrite ?node_48326.
  rewrite ?node_48327.
  rewrite ?node_48328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48330 (s : N.State) (i : N.Inputs) :
  R.v48330 (state s) (inputs i) = Zmod.unsigned (N.v48330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48330 s i)) at 1.
  unfold R.v48330, N.v48330.
  rewrite ?node_48325.
  rewrite ?node_48329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48331 (s : N.State) (i : N.Inputs) :
  R.v48331 (state s) (inputs i) = Zmod.unsigned (N.v48331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48331 s i)) at 1.
  unfold R.v48331, N.v48331.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48332 (s : N.State) (i : N.Inputs) :
  R.v48332 (state s) (inputs i) = Zmod.unsigned (N.v48332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48332 s i)) at 1.
  unfold R.v48332, N.v48332.
  rewrite ?node_15915.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48333 (s : N.State) (i : N.Inputs) :
  R.v48333 (state s) (inputs i) = Zmod.unsigned (N.v48333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48333 s i)) at 1.
  unfold R.v48333, N.v48333.
  unfold R.v6, N.v6.
  rewrite ?node_15911.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48334 (s : N.State) (i : N.Inputs) :
  R.v48334 (state s) (inputs i) = Zmod.unsigned (N.v48334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48334 s i)) at 1.
  unfold R.v48334, N.v48334.
  unfold R.v6, N.v6.
  rewrite ?node_15909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48335 (s : N.State) (i : N.Inputs) :
  R.v48335 (state s) (inputs i) = Zmod.unsigned (N.v48335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48335 s i)) at 1.
  unfold R.v48335, N.v48335.
  rewrite ?node_48333.
  rewrite ?node_48334.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48336 (s : N.State) (i : N.Inputs) :
  R.v48336 (state s) (inputs i) = Zmod.unsigned (N.v48336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48336 s i)) at 1.
  unfold R.v48336, N.v48336.
  unfold R.v16484, N.v16484.
  rewrite ?node_48335.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48337 (s : N.State) (i : N.Inputs) :
  R.v48337 (state s) (inputs i) = Zmod.unsigned (N.v48337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48337 s i)) at 1.
  unfold R.v48337, N.v48337.
  rewrite ?node_48332.
  rewrite ?node_48336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48338 (s : N.State) (i : N.Inputs) :
  R.v48338 (state s) (inputs i) = Zmod.unsigned (N.v48338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48338 s i)) at 1.
  unfold R.v48338, N.v48338.
  unfold R.v6, N.v6.
  rewrite ?node_48337.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48339 (s : N.State) (i : N.Inputs) :
  R.v48339 (state s) (inputs i) = Zmod.unsigned (N.v48339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48339 s i)) at 1.
  unfold R.v48339, N.v48339.
  rewrite ?node_15916.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48340 (s : N.State) (i : N.Inputs) :
  R.v48340 (state s) (inputs i) = Zmod.unsigned (N.v48340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48340 s i)) at 1.
  unfold R.v48340, N.v48340.
  unfold R.v6, N.v6.
  rewrite ?node_15960.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48341 (s : N.State) (i : N.Inputs) :
  R.v48341 (state s) (inputs i) = Zmod.unsigned (N.v48341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48341 s i)) at 1.
  unfold R.v48341, N.v48341.
  rewrite ?node_48339.
  rewrite ?node_48340.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48342 (s : N.State) (i : N.Inputs) :
  R.v48342 (state s) (inputs i) = Zmod.unsigned (N.v48342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48342 s i)) at 1.
  unfold R.v48342, N.v48342.
  rewrite ?node_48338.
  rewrite ?node_48341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48343 (s : N.State) (i : N.Inputs) :
  R.v48343 (state s) (inputs i) = Zmod.unsigned (N.v48343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48343 s i)) at 1.
  unfold R.v48343, N.v48343.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48344 (s : N.State) (i : N.Inputs) :
  R.v48344 (state s) (inputs i) = Zmod.unsigned (N.v48344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48344 s i)) at 1.
  unfold R.v48344, N.v48344.
  rewrite ?node_15923.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48345 (s : N.State) (i : N.Inputs) :
  R.v48345 (state s) (inputs i) = Zmod.unsigned (N.v48345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48345 s i)) at 1.
  unfold R.v48345, N.v48345.
  unfold R.v6, N.v6.
  rewrite ?node_15919.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48346 (s : N.State) (i : N.Inputs) :
  R.v48346 (state s) (inputs i) = Zmod.unsigned (N.v48346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48346 s i)) at 1.
  unfold R.v48346, N.v48346.
  unfold R.v6, N.v6.
  rewrite ?node_15916.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48347 (s : N.State) (i : N.Inputs) :
  R.v48347 (state s) (inputs i) = Zmod.unsigned (N.v48347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48347 s i)) at 1.
  unfold R.v48347, N.v48347.
  rewrite ?node_48345.
  rewrite ?node_48346.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48348 (s : N.State) (i : N.Inputs) :
  R.v48348 (state s) (inputs i) = Zmod.unsigned (N.v48348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48348 s i)) at 1.
  unfold R.v48348, N.v48348.
  unfold R.v16484, N.v16484.
  rewrite ?node_48347.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48349 (s : N.State) (i : N.Inputs) :
  R.v48349 (state s) (inputs i) = Zmod.unsigned (N.v48349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48349 s i)) at 1.
  unfold R.v48349, N.v48349.
  rewrite ?node_48344.
  rewrite ?node_48348.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48350 (s : N.State) (i : N.Inputs) :
  R.v48350 (state s) (inputs i) = Zmod.unsigned (N.v48350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48350 s i)) at 1.
  unfold R.v48350, N.v48350.
  unfold R.v6, N.v6.
  rewrite ?node_48349.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48351 (s : N.State) (i : N.Inputs) :
  R.v48351 (state s) (inputs i) = Zmod.unsigned (N.v48351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48351 s i)) at 1.
  unfold R.v48351, N.v48351.
  rewrite ?node_15924.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48352 (s : N.State) (i : N.Inputs) :
  R.v48352 (state s) (inputs i) = Zmod.unsigned (N.v48352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48352 s i)) at 1.
  unfold R.v48352, N.v48352.
  unfold R.v6, N.v6.
  rewrite ?node_15964.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48353 (s : N.State) (i : N.Inputs) :
  R.v48353 (state s) (inputs i) = Zmod.unsigned (N.v48353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48353 s i)) at 1.
  unfold R.v48353, N.v48353.
  rewrite ?node_48351.
  rewrite ?node_48352.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48354 (s : N.State) (i : N.Inputs) :
  R.v48354 (state s) (inputs i) = Zmod.unsigned (N.v48354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48354 s i)) at 1.
  unfold R.v48354, N.v48354.
  rewrite ?node_48350.
  rewrite ?node_48353.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48355 (s : N.State) (i : N.Inputs) :
  R.v48355 (state s) (inputs i) = Zmod.unsigned (N.v48355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48355 s i)) at 1.
  unfold R.v48355, N.v48355.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48356 (s : N.State) (i : N.Inputs) :
  R.v48356 (state s) (inputs i) = Zmod.unsigned (N.v48356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48356 s i)) at 1.
  unfold R.v48356, N.v48356.
  rewrite ?node_15960.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48357 (s : N.State) (i : N.Inputs) :
  R.v48357 (state s) (inputs i) = Zmod.unsigned (N.v48357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48357 s i)) at 1.
  unfold R.v48357, N.v48357.
  rewrite ?node_15956.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48358 (s : N.State) (i : N.Inputs) :
  R.v48358 (state s) (inputs i) = Zmod.unsigned (N.v48358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48358 s i)) at 1.
  unfold R.v48358, N.v48358.
  rewrite ?node_15952.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48359 (s : N.State) (i : N.Inputs) :
  R.v48359 (state s) (inputs i) = Zmod.unsigned (N.v48359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48359 s i)) at 1.
  unfold R.v48359, N.v48359.
  unfold R.v6, N.v6.
  rewrite ?node_15948.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48360 (s : N.State) (i : N.Inputs) :
  R.v48360 (state s) (inputs i) = Zmod.unsigned (N.v48360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48360 s i)) at 1.
  unfold R.v48360, N.v48360.
  unfold R.v6, N.v6.
  rewrite ?node_15946.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48361 (s : N.State) (i : N.Inputs) :
  R.v48361 (state s) (inputs i) = Zmod.unsigned (N.v48361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48361 s i)) at 1.
  unfold R.v48361, N.v48361.
  rewrite ?node_48359.
  rewrite ?node_48360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48362 (s : N.State) (i : N.Inputs) :
  R.v48362 (state s) (inputs i) = Zmod.unsigned (N.v48362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48362 s i)) at 1.
  unfold R.v48362, N.v48362.
  unfold R.v16484, N.v16484.
  rewrite ?node_48361.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48363 (s : N.State) (i : N.Inputs) :
  R.v48363 (state s) (inputs i) = Zmod.unsigned (N.v48363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48363 s i)) at 1.
  unfold R.v48363, N.v48363.
  rewrite ?node_48356.
  rewrite ?node_48357.
  rewrite ?node_48358.
  rewrite ?node_48362.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48364 (s : N.State) (i : N.Inputs) :
  R.v48364 (state s) (inputs i) = Zmod.unsigned (N.v48364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48364 s i)) at 1.
  unfold R.v48364, N.v48364.
  unfold R.v6, N.v6.
  rewrite ?node_48363.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48365 (s : N.State) (i : N.Inputs) :
  R.v48365 (state s) (inputs i) = Zmod.unsigned (N.v48365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48365 s i)) at 1.
  unfold R.v48365, N.v48365.
  rewrite ?node_15961.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48366 (s : N.State) (i : N.Inputs) :
  R.v48366 (state s) (inputs i) = Zmod.unsigned (N.v48366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48366 s i)) at 1.
  unfold R.v48366, N.v48366.
  unfold R.v6, N.v6.
  rewrite ?node_15993.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48367 (s : N.State) (i : N.Inputs) :
  R.v48367 (state s) (inputs i) = Zmod.unsigned (N.v48367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48367 s i)) at 1.
  unfold R.v48367, N.v48367.
  unfold R.v6, N.v6.
  rewrite ?node_15997.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48368 (s : N.State) (i : N.Inputs) :
  R.v48368 (state s) (inputs i) = Zmod.unsigned (N.v48368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48368 s i)) at 1.
  unfold R.v48368, N.v48368.
  rewrite ?node_48365.
  rewrite ?node_48366.
  rewrite ?node_48367.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48369 (s : N.State) (i : N.Inputs) :
  R.v48369 (state s) (inputs i) = Zmod.unsigned (N.v48369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48369 s i)) at 1.
  unfold R.v48369, N.v48369.
  rewrite ?node_48364.
  rewrite ?node_48368.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48370 (s : N.State) (i : N.Inputs) :
  R.v48370 (state s) (inputs i) = Zmod.unsigned (N.v48370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48370 s i)) at 1.
  unfold R.v48370, N.v48370.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48371 (s : N.State) (i : N.Inputs) :
  R.v48371 (state s) (inputs i) = Zmod.unsigned (N.v48371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48371 s i)) at 1.
  unfold R.v48371, N.v48371.
  rewrite ?node_15952.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48372 (s : N.State) (i : N.Inputs) :
  R.v48372 (state s) (inputs i) = Zmod.unsigned (N.v48372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48372 s i)) at 1.
  unfold R.v48372, N.v48372.
  unfold R.v6, N.v6.
  rewrite ?node_15948.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48373 (s : N.State) (i : N.Inputs) :
  R.v48373 (state s) (inputs i) = Zmod.unsigned (N.v48373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48373 s i)) at 1.
  unfold R.v48373, N.v48373.
  unfold R.v6, N.v6.
  rewrite ?node_15946.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48374 (s : N.State) (i : N.Inputs) :
  R.v48374 (state s) (inputs i) = Zmod.unsigned (N.v48374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48374 s i)) at 1.
  unfold R.v48374, N.v48374.
  rewrite ?node_48372.
  rewrite ?node_48373.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48375 (s : N.State) (i : N.Inputs) :
  R.v48375 (state s) (inputs i) = Zmod.unsigned (N.v48375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48375 s i)) at 1.
  unfold R.v48375, N.v48375.
  unfold R.v16484, N.v16484.
  rewrite ?node_48374.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48376 (s : N.State) (i : N.Inputs) :
  R.v48376 (state s) (inputs i) = Zmod.unsigned (N.v48376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48376 s i)) at 1.
  unfold R.v48376, N.v48376.
  rewrite ?node_48371.
  rewrite ?node_48375.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48377 (s : N.State) (i : N.Inputs) :
  R.v48377 (state s) (inputs i) = Zmod.unsigned (N.v48377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48377 s i)) at 1.
  unfold R.v48377, N.v48377.
  unfold R.v6, N.v6.
  rewrite ?node_48376.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48378 (s : N.State) (i : N.Inputs) :
  R.v48378 (state s) (inputs i) = Zmod.unsigned (N.v48378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48378 s i)) at 1.
  unfold R.v48378, N.v48378.
  rewrite ?node_15953.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48379 (s : N.State) (i : N.Inputs) :
  R.v48379 (state s) (inputs i) = Zmod.unsigned (N.v48379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48379 s i)) at 1.
  unfold R.v48379, N.v48379.
  unfold R.v6, N.v6.
  rewrite ?node_15993.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48380 (s : N.State) (i : N.Inputs) :
  R.v48380 (state s) (inputs i) = Zmod.unsigned (N.v48380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48380 s i)) at 1.
  unfold R.v48380, N.v48380.
  rewrite ?node_48378.
  rewrite ?node_48379.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48381 (s : N.State) (i : N.Inputs) :
  R.v48381 (state s) (inputs i) = Zmod.unsigned (N.v48381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48381 s i)) at 1.
  unfold R.v48381, N.v48381.
  rewrite ?node_48377.
  rewrite ?node_48380.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48382 (s : N.State) (i : N.Inputs) :
  R.v48382 (state s) (inputs i) = Zmod.unsigned (N.v48382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48382 s i)) at 1.
  unfold R.v48382, N.v48382.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48383 (s : N.State) (i : N.Inputs) :
  R.v48383 (state s) (inputs i) = Zmod.unsigned (N.v48383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48383 s i)) at 1.
  unfold R.v48383, N.v48383.
  rewrite ?node_15960.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48384 (s : N.State) (i : N.Inputs) :
  R.v48384 (state s) (inputs i) = Zmod.unsigned (N.v48384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48384 s i)) at 1.
  unfold R.v48384, N.v48384.
  unfold R.v6, N.v6.
  rewrite ?node_15956.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48385 (s : N.State) (i : N.Inputs) :
  R.v48385 (state s) (inputs i) = Zmod.unsigned (N.v48385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48385 s i)) at 1.
  unfold R.v48385, N.v48385.
  unfold R.v6, N.v6.
  rewrite ?node_15953.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48386 (s : N.State) (i : N.Inputs) :
  R.v48386 (state s) (inputs i) = Zmod.unsigned (N.v48386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48386 s i)) at 1.
  unfold R.v48386, N.v48386.
  rewrite ?node_48384.
  rewrite ?node_48385.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48387 (s : N.State) (i : N.Inputs) :
  R.v48387 (state s) (inputs i) = Zmod.unsigned (N.v48387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48387 s i)) at 1.
  unfold R.v48387, N.v48387.
  unfold R.v16484, N.v16484.
  rewrite ?node_48386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48388 (s : N.State) (i : N.Inputs) :
  R.v48388 (state s) (inputs i) = Zmod.unsigned (N.v48388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48388 s i)) at 1.
  unfold R.v48388, N.v48388.
  rewrite ?node_48383.
  rewrite ?node_48387.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48389 (s : N.State) (i : N.Inputs) :
  R.v48389 (state s) (inputs i) = Zmod.unsigned (N.v48389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48389 s i)) at 1.
  unfold R.v48389, N.v48389.
  unfold R.v6, N.v6.
  rewrite ?node_48388.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48390 (s : N.State) (i : N.Inputs) :
  R.v48390 (state s) (inputs i) = Zmod.unsigned (N.v48390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48390 s i)) at 1.
  unfold R.v48390, N.v48390.
  rewrite ?node_15961.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48391 (s : N.State) (i : N.Inputs) :
  R.v48391 (state s) (inputs i) = Zmod.unsigned (N.v48391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48391 s i)) at 1.
  unfold R.v48391, N.v48391.
  unfold R.v6, N.v6.
  rewrite ?node_15997.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48392 (s : N.State) (i : N.Inputs) :
  R.v48392 (state s) (inputs i) = Zmod.unsigned (N.v48392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48392 s i)) at 1.
  unfold R.v48392, N.v48392.
  rewrite ?node_48390.
  rewrite ?node_48391.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48393 (s : N.State) (i : N.Inputs) :
  R.v48393 (state s) (inputs i) = Zmod.unsigned (N.v48393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48393 s i)) at 1.
  unfold R.v48393, N.v48393.
  rewrite ?node_48389.
  rewrite ?node_48392.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48394 (s : N.State) (i : N.Inputs) :
  R.v48394 (state s) (inputs i) = Zmod.unsigned (N.v48394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48394 s i)) at 1.
  unfold R.v48394, N.v48394.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48395 (s : N.State) (i : N.Inputs) :
  R.v48395 (state s) (inputs i) = Zmod.unsigned (N.v48395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48395 s i)) at 1.
  unfold R.v48395, N.v48395.
  rewrite ?node_15993.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48396 (s : N.State) (i : N.Inputs) :
  R.v48396 (state s) (inputs i) = Zmod.unsigned (N.v48396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48396 s i)) at 1.
  unfold R.v48396, N.v48396.
  rewrite ?node_15989.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48397 (s : N.State) (i : N.Inputs) :
  R.v48397 (state s) (inputs i) = Zmod.unsigned (N.v48397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48397 s i)) at 1.
  unfold R.v48397, N.v48397.
  rewrite ?node_15985.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48398 (s : N.State) (i : N.Inputs) :
  R.v48398 (state s) (inputs i) = Zmod.unsigned (N.v48398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48398 s i)) at 1.
  unfold R.v48398, N.v48398.
  unfold R.v6, N.v6.
  rewrite ?node_15981.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48399 (s : N.State) (i : N.Inputs) :
  R.v48399 (state s) (inputs i) = Zmod.unsigned (N.v48399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48399 s i)) at 1.
  unfold R.v48399, N.v48399.
  unfold R.v6, N.v6.
  rewrite ?node_15980.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48400 (s : N.State) (i : N.Inputs) :
  R.v48400 (state s) (inputs i) = Zmod.unsigned (N.v48400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48400 s i)) at 1.
  unfold R.v48400, N.v48400.
  rewrite ?node_48398.
  rewrite ?node_48399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48401 (s : N.State) (i : N.Inputs) :
  R.v48401 (state s) (inputs i) = Zmod.unsigned (N.v48401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48401 s i)) at 1.
  unfold R.v48401, N.v48401.
  unfold R.v16484, N.v16484.
  rewrite ?node_48400.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48402 (s : N.State) (i : N.Inputs) :
  R.v48402 (state s) (inputs i) = Zmod.unsigned (N.v48402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48402 s i)) at 1.
  unfold R.v48402, N.v48402.
  rewrite ?node_48395.
  rewrite ?node_48396.
  rewrite ?node_48397.
  rewrite ?node_48401.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48403 (s : N.State) (i : N.Inputs) :
  R.v48403 (state s) (inputs i) = Zmod.unsigned (N.v48403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48403 s i)) at 1.
  unfold R.v48403, N.v48403.
  unfold R.v6, N.v6.
  rewrite ?node_48402.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48404 (s : N.State) (i : N.Inputs) :
  R.v48404 (state s) (inputs i) = Zmod.unsigned (N.v48404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48404 s i)) at 1.
  unfold R.v48404, N.v48404.
  rewrite ?node_15994.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48405 (s : N.State) (i : N.Inputs) :
  R.v48405 (state s) (inputs i) = Zmod.unsigned (N.v48405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48405 s i)) at 1.
  unfold R.v48405, N.v48405.
  unfold R.v6, N.v6.
  rewrite ?node_16023.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48406 (s : N.State) (i : N.Inputs) :
  R.v48406 (state s) (inputs i) = Zmod.unsigned (N.v48406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48406 s i)) at 1.
  unfold R.v48406, N.v48406.
  unfold R.v6, N.v6.
  rewrite ?node_16027.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48407 (s : N.State) (i : N.Inputs) :
  R.v48407 (state s) (inputs i) = Zmod.unsigned (N.v48407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48407 s i)) at 1.
  unfold R.v48407, N.v48407.
  rewrite ?node_48404.
  rewrite ?node_48405.
  rewrite ?node_48406.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48408 (s : N.State) (i : N.Inputs) :
  R.v48408 (state s) (inputs i) = Zmod.unsigned (N.v48408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48408 s i)) at 1.
  unfold R.v48408, N.v48408.
  rewrite ?node_48403.
  rewrite ?node_48407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48409 (s : N.State) (i : N.Inputs) :
  R.v48409 (state s) (inputs i) = Zmod.unsigned (N.v48409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48409 s i)) at 1.
  unfold R.v48409, N.v48409.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48410 (s : N.State) (i : N.Inputs) :
  R.v48410 (state s) (inputs i) = Zmod.unsigned (N.v48410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48410 s i)) at 1.
  unfold R.v48410, N.v48410.
  rewrite ?node_15985.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48411 (s : N.State) (i : N.Inputs) :
  R.v48411 (state s) (inputs i) = Zmod.unsigned (N.v48411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48411 s i)) at 1.
  unfold R.v48411, N.v48411.
  unfold R.v6, N.v6.
  rewrite ?node_15981.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48412 (s : N.State) (i : N.Inputs) :
  R.v48412 (state s) (inputs i) = Zmod.unsigned (N.v48412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48412 s i)) at 1.
  unfold R.v48412, N.v48412.
  unfold R.v6, N.v6.
  rewrite ?node_15980.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48413 (s : N.State) (i : N.Inputs) :
  R.v48413 (state s) (inputs i) = Zmod.unsigned (N.v48413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48413 s i)) at 1.
  unfold R.v48413, N.v48413.
  rewrite ?node_48411.
  rewrite ?node_48412.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48414 (s : N.State) (i : N.Inputs) :
  R.v48414 (state s) (inputs i) = Zmod.unsigned (N.v48414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48414 s i)) at 1.
  unfold R.v48414, N.v48414.
  unfold R.v16484, N.v16484.
  rewrite ?node_48413.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48415 (s : N.State) (i : N.Inputs) :
  R.v48415 (state s) (inputs i) = Zmod.unsigned (N.v48415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48415 s i)) at 1.
  unfold R.v48415, N.v48415.
  rewrite ?node_48410.
  rewrite ?node_48414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48416 (s : N.State) (i : N.Inputs) :
  R.v48416 (state s) (inputs i) = Zmod.unsigned (N.v48416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48416 s i)) at 1.
  unfold R.v48416, N.v48416.
  unfold R.v6, N.v6.
  rewrite ?node_48415.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48417 (s : N.State) (i : N.Inputs) :
  R.v48417 (state s) (inputs i) = Zmod.unsigned (N.v48417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48417 s i)) at 1.
  unfold R.v48417, N.v48417.
  rewrite ?node_15986.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48418 (s : N.State) (i : N.Inputs) :
  R.v48418 (state s) (inputs i) = Zmod.unsigned (N.v48418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48418 s i)) at 1.
  unfold R.v48418, N.v48418.
  unfold R.v6, N.v6.
  rewrite ?node_16023.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48419 (s : N.State) (i : N.Inputs) :
  R.v48419 (state s) (inputs i) = Zmod.unsigned (N.v48419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48419 s i)) at 1.
  unfold R.v48419, N.v48419.
  rewrite ?node_48417.
  rewrite ?node_48418.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48420 (s : N.State) (i : N.Inputs) :
  R.v48420 (state s) (inputs i) = Zmod.unsigned (N.v48420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48420 s i)) at 1.
  unfold R.v48420, N.v48420.
  rewrite ?node_48416.
  rewrite ?node_48419.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48421 (s : N.State) (i : N.Inputs) :
  R.v48421 (state s) (inputs i) = Zmod.unsigned (N.v48421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48421 s i)) at 1.
  unfold R.v48421, N.v48421.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48422 (s : N.State) (i : N.Inputs) :
  R.v48422 (state s) (inputs i) = Zmod.unsigned (N.v48422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48422 s i)) at 1.
  unfold R.v48422, N.v48422.
  rewrite ?node_15993.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48423 (s : N.State) (i : N.Inputs) :
  R.v48423 (state s) (inputs i) = Zmod.unsigned (N.v48423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48423 s i)) at 1.
  unfold R.v48423, N.v48423.
  unfold R.v6, N.v6.
  rewrite ?node_15989.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48424 (s : N.State) (i : N.Inputs) :
  R.v48424 (state s) (inputs i) = Zmod.unsigned (N.v48424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48424 s i)) at 1.
  unfold R.v48424, N.v48424.
  unfold R.v6, N.v6.
  rewrite ?node_15986.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48425 (s : N.State) (i : N.Inputs) :
  R.v48425 (state s) (inputs i) = Zmod.unsigned (N.v48425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48425 s i)) at 1.
  unfold R.v48425, N.v48425.
  rewrite ?node_48423.
  rewrite ?node_48424.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48426 (s : N.State) (i : N.Inputs) :
  R.v48426 (state s) (inputs i) = Zmod.unsigned (N.v48426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48426 s i)) at 1.
  unfold R.v48426, N.v48426.
  unfold R.v16484, N.v16484.
  rewrite ?node_48425.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48427 (s : N.State) (i : N.Inputs) :
  R.v48427 (state s) (inputs i) = Zmod.unsigned (N.v48427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48427 s i)) at 1.
  unfold R.v48427, N.v48427.
  rewrite ?node_48422.
  rewrite ?node_48426.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48428 (s : N.State) (i : N.Inputs) :
  R.v48428 (state s) (inputs i) = Zmod.unsigned (N.v48428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48428 s i)) at 1.
  unfold R.v48428, N.v48428.
  unfold R.v6, N.v6.
  rewrite ?node_48427.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48429 (s : N.State) (i : N.Inputs) :
  R.v48429 (state s) (inputs i) = Zmod.unsigned (N.v48429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48429 s i)) at 1.
  unfold R.v48429, N.v48429.
  rewrite ?node_15994.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48430 (s : N.State) (i : N.Inputs) :
  R.v48430 (state s) (inputs i) = Zmod.unsigned (N.v48430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48430 s i)) at 1.
  unfold R.v48430, N.v48430.
  unfold R.v6, N.v6.
  rewrite ?node_16027.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48431 (s : N.State) (i : N.Inputs) :
  R.v48431 (state s) (inputs i) = Zmod.unsigned (N.v48431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48431 s i)) at 1.
  unfold R.v48431, N.v48431.
  rewrite ?node_48429.
  rewrite ?node_48430.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48432 (s : N.State) (i : N.Inputs) :
  R.v48432 (state s) (inputs i) = Zmod.unsigned (N.v48432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48432 s i)) at 1.
  unfold R.v48432, N.v48432.
  rewrite ?node_48428.
  rewrite ?node_48431.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48433 (s : N.State) (i : N.Inputs) :
  R.v48433 (state s) (inputs i) = Zmod.unsigned (N.v48433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48433 s i)) at 1.
  unfold R.v48433, N.v48433.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48434 (s : N.State) (i : N.Inputs) :
  R.v48434 (state s) (inputs i) = Zmod.unsigned (N.v48434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48434 s i)) at 1.
  unfold R.v48434, N.v48434.
  rewrite ?node_16023.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48435 (s : N.State) (i : N.Inputs) :
  R.v48435 (state s) (inputs i) = Zmod.unsigned (N.v48435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48435 s i)) at 1.
  unfold R.v48435, N.v48435.
  rewrite ?node_16019.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48436 (s : N.State) (i : N.Inputs) :
  R.v48436 (state s) (inputs i) = Zmod.unsigned (N.v48436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48436 s i)) at 1.
  unfold R.v48436, N.v48436.
  rewrite ?node_16017.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48437 (s : N.State) (i : N.Inputs) :
  R.v48437 (state s) (inputs i) = Zmod.unsigned (N.v48437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48437 s i)) at 1.
  unfold R.v48437, N.v48437.
  unfold R.v6, N.v6.
  rewrite ?node_16013.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48438 (s : N.State) (i : N.Inputs) :
  R.v48438 (state s) (inputs i) = Zmod.unsigned (N.v48438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48438 s i)) at 1.
  unfold R.v48438, N.v48438.
  unfold R.v6, N.v6.
  rewrite ?node_16012.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48439 (s : N.State) (i : N.Inputs) :
  R.v48439 (state s) (inputs i) = Zmod.unsigned (N.v48439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48439 s i)) at 1.
  unfold R.v48439, N.v48439.
  rewrite ?node_48437.
  rewrite ?node_48438.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48440 (s : N.State) (i : N.Inputs) :
  R.v48440 (state s) (inputs i) = Zmod.unsigned (N.v48440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48440 s i)) at 1.
  unfold R.v48440, N.v48440.
  unfold R.v16484, N.v16484.
  rewrite ?node_48439.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48441 (s : N.State) (i : N.Inputs) :
  R.v48441 (state s) (inputs i) = Zmod.unsigned (N.v48441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48441 s i)) at 1.
  unfold R.v48441, N.v48441.
  rewrite ?node_48434.
  rewrite ?node_48435.
  rewrite ?node_48436.
  rewrite ?node_48440.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48442 (s : N.State) (i : N.Inputs) :
  R.v48442 (state s) (inputs i) = Zmod.unsigned (N.v48442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48442 s i)) at 1.
  unfold R.v48442, N.v48442.
  unfold R.v6, N.v6.
  rewrite ?node_48441.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48443 (s : N.State) (i : N.Inputs) :
  R.v48443 (state s) (inputs i) = Zmod.unsigned (N.v48443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48443 s i)) at 1.
  unfold R.v48443, N.v48443.
  rewrite ?node_16024.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48444 (s : N.State) (i : N.Inputs) :
  R.v48444 (state s) (inputs i) = Zmod.unsigned (N.v48444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48444 s i)) at 1.
  unfold R.v48444, N.v48444.
  unfold R.v6, N.v6.
  rewrite ?node_16051.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48445 (s : N.State) (i : N.Inputs) :
  R.v48445 (state s) (inputs i) = Zmod.unsigned (N.v48445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48445 s i)) at 1.
  unfold R.v48445, N.v48445.
  unfold R.v6, N.v6.
  rewrite ?node_16055.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48446 (s : N.State) (i : N.Inputs) :
  R.v48446 (state s) (inputs i) = Zmod.unsigned (N.v48446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48446 s i)) at 1.
  unfold R.v48446, N.v48446.
  rewrite ?node_48443.
  rewrite ?node_48444.
  rewrite ?node_48445.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48447 (s : N.State) (i : N.Inputs) :
  R.v48447 (state s) (inputs i) = Zmod.unsigned (N.v48447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48447 s i)) at 1.
  unfold R.v48447, N.v48447.
  rewrite ?node_48442.
  rewrite ?node_48446.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48448 (s : N.State) (i : N.Inputs) :
  R.v48448 (state s) (inputs i) = Zmod.unsigned (N.v48448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48448 s i)) at 1.
  unfold R.v48448, N.v48448.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48449 (s : N.State) (i : N.Inputs) :
  R.v48449 (state s) (inputs i) = Zmod.unsigned (N.v48449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48449 s i)) at 1.
  unfold R.v48449, N.v48449.
  rewrite ?node_16017.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48450 (s : N.State) (i : N.Inputs) :
  R.v48450 (state s) (inputs i) = Zmod.unsigned (N.v48450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48450 s i)) at 1.
  unfold R.v48450, N.v48450.
  unfold R.v6, N.v6.
  rewrite ?node_16013.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48451 (s : N.State) (i : N.Inputs) :
  R.v48451 (state s) (inputs i) = Zmod.unsigned (N.v48451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48451 s i)) at 1.
  unfold R.v48451, N.v48451.
  unfold R.v6, N.v6.
  rewrite ?node_16012.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48452 (s : N.State) (i : N.Inputs) :
  R.v48452 (state s) (inputs i) = Zmod.unsigned (N.v48452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48452 s i)) at 1.
  unfold R.v48452, N.v48452.
  rewrite ?node_48450.
  rewrite ?node_48451.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48453 (s : N.State) (i : N.Inputs) :
  R.v48453 (state s) (inputs i) = Zmod.unsigned (N.v48453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48453 s i)) at 1.
  unfold R.v48453, N.v48453.
  unfold R.v16484, N.v16484.
  rewrite ?node_48452.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48454 (s : N.State) (i : N.Inputs) :
  R.v48454 (state s) (inputs i) = Zmod.unsigned (N.v48454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48454 s i)) at 1.
  unfold R.v48454, N.v48454.
  rewrite ?node_48449.
  rewrite ?node_48453.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48455 (s : N.State) (i : N.Inputs) :
  R.v48455 (state s) (inputs i) = Zmod.unsigned (N.v48455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48455 s i)) at 1.
  unfold R.v48455, N.v48455.
  unfold R.v6, N.v6.
  rewrite ?node_48454.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48456 (s : N.State) (i : N.Inputs) :
  R.v48456 (state s) (inputs i) = Zmod.unsigned (N.v48456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48456 s i)) at 1.
  unfold R.v48456, N.v48456.
  rewrite ?node_16018.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48457 (s : N.State) (i : N.Inputs) :
  R.v48457 (state s) (inputs i) = Zmod.unsigned (N.v48457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48457 s i)) at 1.
  unfold R.v48457, N.v48457.
  unfold R.v6, N.v6.
  rewrite ?node_16051.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48458 (s : N.State) (i : N.Inputs) :
  R.v48458 (state s) (inputs i) = Zmod.unsigned (N.v48458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48458 s i)) at 1.
  unfold R.v48458, N.v48458.
  rewrite ?node_48456.
  rewrite ?node_48457.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48459 (s : N.State) (i : N.Inputs) :
  R.v48459 (state s) (inputs i) = Zmod.unsigned (N.v48459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48459 s i)) at 1.
  unfold R.v48459, N.v48459.
  rewrite ?node_48455.
  rewrite ?node_48458.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48460 (s : N.State) (i : N.Inputs) :
  R.v48460 (state s) (inputs i) = Zmod.unsigned (N.v48460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48460 s i)) at 1.
  unfold R.v48460, N.v48460.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48461 (s : N.State) (i : N.Inputs) :
  R.v48461 (state s) (inputs i) = Zmod.unsigned (N.v48461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48461 s i)) at 1.
  unfold R.v48461, N.v48461.
  rewrite ?node_16023.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48462 (s : N.State) (i : N.Inputs) :
  R.v48462 (state s) (inputs i) = Zmod.unsigned (N.v48462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48462 s i)) at 1.
  unfold R.v48462, N.v48462.
  unfold R.v6, N.v6.
  rewrite ?node_16019.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48463 (s : N.State) (i : N.Inputs) :
  R.v48463 (state s) (inputs i) = Zmod.unsigned (N.v48463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48463 s i)) at 1.
  unfold R.v48463, N.v48463.
  unfold R.v6, N.v6.
  rewrite ?node_16018.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48464 (s : N.State) (i : N.Inputs) :
  R.v48464 (state s) (inputs i) = Zmod.unsigned (N.v48464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48464 s i)) at 1.
  unfold R.v48464, N.v48464.
  rewrite ?node_48462.
  rewrite ?node_48463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48465 (s : N.State) (i : N.Inputs) :
  R.v48465 (state s) (inputs i) = Zmod.unsigned (N.v48465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48465 s i)) at 1.
  unfold R.v48465, N.v48465.
  unfold R.v16484, N.v16484.
  rewrite ?node_48464.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48466 (s : N.State) (i : N.Inputs) :
  R.v48466 (state s) (inputs i) = Zmod.unsigned (N.v48466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48466 s i)) at 1.
  unfold R.v48466, N.v48466.
  rewrite ?node_48461.
  rewrite ?node_48465.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48467 (s : N.State) (i : N.Inputs) :
  R.v48467 (state s) (inputs i) = Zmod.unsigned (N.v48467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48467 s i)) at 1.
  unfold R.v48467, N.v48467.
  unfold R.v6, N.v6.
  rewrite ?node_48466.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48468 (s : N.State) (i : N.Inputs) :
  R.v48468 (state s) (inputs i) = Zmod.unsigned (N.v48468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48468 s i)) at 1.
  unfold R.v48468, N.v48468.
  rewrite ?node_16024.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48469 (s : N.State) (i : N.Inputs) :
  R.v48469 (state s) (inputs i) = Zmod.unsigned (N.v48469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48469 s i)) at 1.
  unfold R.v48469, N.v48469.
  unfold R.v6, N.v6.
  rewrite ?node_16055.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48470 (s : N.State) (i : N.Inputs) :
  R.v48470 (state s) (inputs i) = Zmod.unsigned (N.v48470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48470 s i)) at 1.
  unfold R.v48470, N.v48470.
  rewrite ?node_48468.
  rewrite ?node_48469.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48471 (s : N.State) (i : N.Inputs) :
  R.v48471 (state s) (inputs i) = Zmod.unsigned (N.v48471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48471 s i)) at 1.
  unfold R.v48471, N.v48471.
  rewrite ?node_48467.
  rewrite ?node_48470.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48472 (s : N.State) (i : N.Inputs) :
  R.v48472 (state s) (inputs i) = Zmod.unsigned (N.v48472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48472 s i)) at 1.
  unfold R.v48472, N.v48472.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48473 (s : N.State) (i : N.Inputs) :
  R.v48473 (state s) (inputs i) = Zmod.unsigned (N.v48473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48473 s i)) at 1.
  unfold R.v48473, N.v48473.
  rewrite ?node_16051.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48474 (s : N.State) (i : N.Inputs) :
  R.v48474 (state s) (inputs i) = Zmod.unsigned (N.v48474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48474 s i)) at 1.
  unfold R.v48474, N.v48474.
  rewrite ?node_16047.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48475 (s : N.State) (i : N.Inputs) :
  R.v48475 (state s) (inputs i) = Zmod.unsigned (N.v48475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48475 s i)) at 1.
  unfold R.v48475, N.v48475.
  rewrite ?node_16045.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48476 (s : N.State) (i : N.Inputs) :
  R.v48476 (state s) (inputs i) = Zmod.unsigned (N.v48476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48476 s i)) at 1.
  unfold R.v48476, N.v48476.
  unfold R.v6, N.v6.
  rewrite !state_r2258_nr_5F2285.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2258_nr_5F2285 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48477 (s : N.State) (i : N.Inputs) :
  R.v48477 (state s) (inputs i) = Zmod.unsigned (N.v48477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48477 s i)) at 1.
  unfold R.v48477, N.v48477.
  unfold R.v6, N.v6.
  rewrite ?node_16041.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48478 (s : N.State) (i : N.Inputs) :
  R.v48478 (state s) (inputs i) = Zmod.unsigned (N.v48478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48478 s i)) at 1.
  unfold R.v48478, N.v48478.
  rewrite ?node_48476.
  rewrite ?node_48477.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48479 (s : N.State) (i : N.Inputs) :
  R.v48479 (state s) (inputs i) = Zmod.unsigned (N.v48479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48479 s i)) at 1.
  unfold R.v48479, N.v48479.
  unfold R.v16484, N.v16484.
  rewrite ?node_48478.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48480 (s : N.State) (i : N.Inputs) :
  R.v48480 (state s) (inputs i) = Zmod.unsigned (N.v48480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48480 s i)) at 1.
  unfold R.v48480, N.v48480.
  rewrite ?node_48473.
  rewrite ?node_48474.
  rewrite ?node_48475.
  rewrite ?node_48479.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48481 (s : N.State) (i : N.Inputs) :
  R.v48481 (state s) (inputs i) = Zmod.unsigned (N.v48481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48481 s i)) at 1.
  unfold R.v48481, N.v48481.
  unfold R.v6, N.v6.
  rewrite ?node_48480.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48482 (s : N.State) (i : N.Inputs) :
  R.v48482 (state s) (inputs i) = Zmod.unsigned (N.v48482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48482 s i)) at 1.
  unfold R.v48482, N.v48482.
  rewrite ?node_16052.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48483 (s : N.State) (i : N.Inputs) :
  R.v48483 (state s) (inputs i) = Zmod.unsigned (N.v48483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48483 s i)) at 1.
  unfold R.v48483, N.v48483.
  unfold R.v6, N.v6.
  rewrite ?node_16078.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48484 (s : N.State) (i : N.Inputs) :
  R.v48484 (state s) (inputs i) = Zmod.unsigned (N.v48484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48484 s i)) at 1.
  unfold R.v48484, N.v48484.
  unfold R.v6, N.v6.
  rewrite ?node_16082.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48485 (s : N.State) (i : N.Inputs) :
  R.v48485 (state s) (inputs i) = Zmod.unsigned (N.v48485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48485 s i)) at 1.
  unfold R.v48485, N.v48485.
  rewrite ?node_48482.
  rewrite ?node_48483.
  rewrite ?node_48484.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48486 (s : N.State) (i : N.Inputs) :
  R.v48486 (state s) (inputs i) = Zmod.unsigned (N.v48486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48486 s i)) at 1.
  unfold R.v48486, N.v48486.
  rewrite ?node_48481.
  rewrite ?node_48485.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48487 (s : N.State) (i : N.Inputs) :
  R.v48487 (state s) (inputs i) = Zmod.unsigned (N.v48487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48487 s i)) at 1.
  unfold R.v48487, N.v48487.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48488 (s : N.State) (i : N.Inputs) :
  R.v48488 (state s) (inputs i) = Zmod.unsigned (N.v48488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48488 s i)) at 1.
  unfold R.v48488, N.v48488.
  rewrite ?node_16045.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48489 (s : N.State) (i : N.Inputs) :
  R.v48489 (state s) (inputs i) = Zmod.unsigned (N.v48489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48489 s i)) at 1.
  unfold R.v48489, N.v48489.
  unfold R.v6, N.v6.
  rewrite !state_r2258_nr_5F2285.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2258_nr_5F2285 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48490 (s : N.State) (i : N.Inputs) :
  R.v48490 (state s) (inputs i) = Zmod.unsigned (N.v48490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48490 s i)) at 1.
  unfold R.v48490, N.v48490.
  unfold R.v6, N.v6.
  rewrite ?node_16041.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48491 (s : N.State) (i : N.Inputs) :
  R.v48491 (state s) (inputs i) = Zmod.unsigned (N.v48491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48491 s i)) at 1.
  unfold R.v48491, N.v48491.
  rewrite ?node_48489.
  rewrite ?node_48490.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48492 (s : N.State) (i : N.Inputs) :
  R.v48492 (state s) (inputs i) = Zmod.unsigned (N.v48492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48492 s i)) at 1.
  unfold R.v48492, N.v48492.
  unfold R.v16484, N.v16484.
  rewrite ?node_48491.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48493 (s : N.State) (i : N.Inputs) :
  R.v48493 (state s) (inputs i) = Zmod.unsigned (N.v48493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48493 s i)) at 1.
  unfold R.v48493, N.v48493.
  rewrite ?node_48488.
  rewrite ?node_48492.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48494 (s : N.State) (i : N.Inputs) :
  R.v48494 (state s) (inputs i) = Zmod.unsigned (N.v48494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48494 s i)) at 1.
  unfold R.v48494, N.v48494.
  unfold R.v6, N.v6.
  rewrite ?node_48493.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48495 (s : N.State) (i : N.Inputs) :
  R.v48495 (state s) (inputs i) = Zmod.unsigned (N.v48495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48495 s i)) at 1.
  unfold R.v48495, N.v48495.
  rewrite ?node_16046.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48496 (s : N.State) (i : N.Inputs) :
  R.v48496 (state s) (inputs i) = Zmod.unsigned (N.v48496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48496 s i)) at 1.
  unfold R.v48496, N.v48496.
  unfold R.v6, N.v6.
  rewrite ?node_16078.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48497 (s : N.State) (i : N.Inputs) :
  R.v48497 (state s) (inputs i) = Zmod.unsigned (N.v48497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48497 s i)) at 1.
  unfold R.v48497, N.v48497.
  rewrite ?node_48495.
  rewrite ?node_48496.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48498 (s : N.State) (i : N.Inputs) :
  R.v48498 (state s) (inputs i) = Zmod.unsigned (N.v48498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48498 s i)) at 1.
  unfold R.v48498, N.v48498.
  rewrite ?node_48494.
  rewrite ?node_48497.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48499 (s : N.State) (i : N.Inputs) :
  R.v48499 (state s) (inputs i) = Zmod.unsigned (N.v48499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48499 s i)) at 1.
  unfold R.v48499, N.v48499.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48500 (s : N.State) (i : N.Inputs) :
  R.v48500 (state s) (inputs i) = Zmod.unsigned (N.v48500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48500 s i)) at 1.
  unfold R.v48500, N.v48500.
  rewrite ?node_16051.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48501 (s : N.State) (i : N.Inputs) :
  R.v48501 (state s) (inputs i) = Zmod.unsigned (N.v48501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48501 s i)) at 1.
  unfold R.v48501, N.v48501.
  unfold R.v6, N.v6.
  rewrite ?node_16047.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48502 (s : N.State) (i : N.Inputs) :
  R.v48502 (state s) (inputs i) = Zmod.unsigned (N.v48502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48502 s i)) at 1.
  unfold R.v48502, N.v48502.
  unfold R.v6, N.v6.
  rewrite ?node_16046.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48503 (s : N.State) (i : N.Inputs) :
  R.v48503 (state s) (inputs i) = Zmod.unsigned (N.v48503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48503 s i)) at 1.
  unfold R.v48503, N.v48503.
  rewrite ?node_48501.
  rewrite ?node_48502.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48504 (s : N.State) (i : N.Inputs) :
  R.v48504 (state s) (inputs i) = Zmod.unsigned (N.v48504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48504 s i)) at 1.
  unfold R.v48504, N.v48504.
  unfold R.v16484, N.v16484.
  rewrite ?node_48503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48505 (s : N.State) (i : N.Inputs) :
  R.v48505 (state s) (inputs i) = Zmod.unsigned (N.v48505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48505 s i)) at 1.
  unfold R.v48505, N.v48505.
  rewrite ?node_48500.
  rewrite ?node_48504.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48506 (s : N.State) (i : N.Inputs) :
  R.v48506 (state s) (inputs i) = Zmod.unsigned (N.v48506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48506 s i)) at 1.
  unfold R.v48506, N.v48506.
  unfold R.v6, N.v6.
  rewrite ?node_48505.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48507 (s : N.State) (i : N.Inputs) :
  R.v48507 (state s) (inputs i) = Zmod.unsigned (N.v48507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48507 s i)) at 1.
  unfold R.v48507, N.v48507.
  rewrite ?node_16052.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48508 (s : N.State) (i : N.Inputs) :
  R.v48508 (state s) (inputs i) = Zmod.unsigned (N.v48508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48508 s i)) at 1.
  unfold R.v48508, N.v48508.
  unfold R.v6, N.v6.
  rewrite ?node_16082.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48509 (s : N.State) (i : N.Inputs) :
  R.v48509 (state s) (inputs i) = Zmod.unsigned (N.v48509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48509 s i)) at 1.
  unfold R.v48509, N.v48509.
  rewrite ?node_48507.
  rewrite ?node_48508.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48510 (s : N.State) (i : N.Inputs) :
  R.v48510 (state s) (inputs i) = Zmod.unsigned (N.v48510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48510 s i)) at 1.
  unfold R.v48510, N.v48510.
  rewrite ?node_48506.
  rewrite ?node_48509.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48511 (s : N.State) (i : N.Inputs) :
  R.v48511 (state s) (inputs i) = Zmod.unsigned (N.v48511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48511 s i)) at 1.
  unfold R.v48511, N.v48511.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48512 (s : N.State) (i : N.Inputs) :
  R.v48512 (state s) (inputs i) = Zmod.unsigned (N.v48512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48512 s i)) at 1.
  unfold R.v48512, N.v48512.
  rewrite ?node_16074.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48513 (s : N.State) (i : N.Inputs) :
  R.v48513 (state s) (inputs i) = Zmod.unsigned (N.v48513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48513 s i)) at 1.
  unfold R.v48513, N.v48513.
  unfold R.v6, N.v6.
  rewrite !state_r2262_nr_5F2290.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2262_nr_5F2290 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48514 (s : N.State) (i : N.Inputs) :
  R.v48514 (state s) (inputs i) = Zmod.unsigned (N.v48514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48514 s i)) at 1.
  unfold R.v48514, N.v48514.
  unfold R.v6, N.v6.
  rewrite ?node_16070.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48515 (s : N.State) (i : N.Inputs) :
  R.v48515 (state s) (inputs i) = Zmod.unsigned (N.v48515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48515 s i)) at 1.
  unfold R.v48515, N.v48515.
  rewrite ?node_48513.
  rewrite ?node_48514.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48516 (s : N.State) (i : N.Inputs) :
  R.v48516 (state s) (inputs i) = Zmod.unsigned (N.v48516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48516 s i)) at 1.
  unfold R.v48516, N.v48516.
  unfold R.v16484, N.v16484.
  rewrite ?node_48515.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48517 (s : N.State) (i : N.Inputs) :
  R.v48517 (state s) (inputs i) = Zmod.unsigned (N.v48517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48517 s i)) at 1.
  unfold R.v48517, N.v48517.
  rewrite ?node_48512.
  rewrite ?node_48516.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48518 (s : N.State) (i : N.Inputs) :
  R.v48518 (state s) (inputs i) = Zmod.unsigned (N.v48518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48518 s i)) at 1.
  unfold R.v48518, N.v48518.
  unfold R.v6, N.v6.
  rewrite ?node_48517.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48519 (s : N.State) (i : N.Inputs) :
  R.v48519 (state s) (inputs i) = Zmod.unsigned (N.v48519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48519 s i)) at 1.
  unfold R.v48519, N.v48519.
  rewrite ?node_16075.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48520 (s : N.State) (i : N.Inputs) :
  R.v48520 (state s) (inputs i) = Zmod.unsigned (N.v48520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48520 s i)) at 1.
  unfold R.v48520, N.v48520.
  unfold R.v6, N.v6.
  rewrite ?node_16103.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48521 (s : N.State) (i : N.Inputs) :
  R.v48521 (state s) (inputs i) = Zmod.unsigned (N.v48521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48521 s i)) at 1.
  unfold R.v48521, N.v48521.
  rewrite ?node_48519.
  rewrite ?node_48520.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48522 (s : N.State) (i : N.Inputs) :
  R.v48522 (state s) (inputs i) = Zmod.unsigned (N.v48522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48522 s i)) at 1.
  unfold R.v48522, N.v48522.
  rewrite ?node_48518.
  rewrite ?node_48521.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48523 (s : N.State) (i : N.Inputs) :
  R.v48523 (state s) (inputs i) = Zmod.unsigned (N.v48523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48523 s i)) at 1.
  unfold R.v48523, N.v48523.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48524 (s : N.State) (i : N.Inputs) :
  R.v48524 (state s) (inputs i) = Zmod.unsigned (N.v48524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48524 s i)) at 1.
  unfold R.v48524, N.v48524.
  unfold R.v6, N.v6.
  rewrite ?node_16099.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48525 (s : N.State) (i : N.Inputs) :
  R.v48525 (state s) (inputs i) = Zmod.unsigned (N.v48525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48525 s i)) at 1.
  unfold R.v48525, N.v48525.
  unfold R.v6, N.v6.
  rewrite ?node_16096.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48526 (s : N.State) (i : N.Inputs) :
  R.v48526 (state s) (inputs i) = Zmod.unsigned (N.v48526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48526 s i)) at 1.
  unfold R.v48526, N.v48526.
  rewrite ?node_48524.
  rewrite ?node_48525.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48527 (s : N.State) (i : N.Inputs) :
  R.v48527 (state s) (inputs i) = Zmod.unsigned (N.v48527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48527 s i)) at 1.
  unfold R.v48527, N.v48527.
  unfold R.v16463, N.v16463.
  rewrite ?node_48526.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48528 (s : N.State) (i : N.Inputs) :
  R.v48528 (state s) (inputs i) = Zmod.unsigned (N.v48528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48528 s i)) at 1.
  unfold R.v48528, N.v48528.
  rewrite ?node_16100.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48529 (s : N.State) (i : N.Inputs) :
  R.v48529 (state s) (inputs i) = Zmod.unsigned (N.v48529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48529 s i)) at 1.
  unfold R.v48529, N.v48529.
  unfold R.v6, N.v6.
  rewrite ?node_16125.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48530 (s : N.State) (i : N.Inputs) :
  R.v48530 (state s) (inputs i) = Zmod.unsigned (N.v48530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48530 s i)) at 1.
  unfold R.v48530, N.v48530.
  rewrite ?node_48528.
  rewrite ?node_48529.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48531 (s : N.State) (i : N.Inputs) :
  R.v48531 (state s) (inputs i) = Zmod.unsigned (N.v48531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48531 s i)) at 1.
  unfold R.v48531, N.v48531.
  rewrite ?node_48527.
  rewrite ?node_48530.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48532 (s : N.State) (i : N.Inputs) :
  R.v48532 (state s) (inputs i) = Zmod.unsigned (N.v48532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48532 s i)) at 1.
  unfold R.v48532, N.v48532.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48533 (s : N.State) (i : N.Inputs) :
  R.v48533 (state s) (inputs i) = Zmod.unsigned (N.v48533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48533 s i)) at 1.
  unfold R.v48533, N.v48533.
  unfold R.v6, N.v6.
  rewrite ?node_16123.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48534 (s : N.State) (i : N.Inputs) :
  R.v48534 (state s) (inputs i) = Zmod.unsigned (N.v48534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48534 s i)) at 1.
  unfold R.v48534, N.v48534.
  unfold R.v6, N.v6.
  rewrite ?node_16120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48535 (s : N.State) (i : N.Inputs) :
  R.v48535 (state s) (inputs i) = Zmod.unsigned (N.v48535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48535 s i)) at 1.
  unfold R.v48535, N.v48535.
  rewrite ?node_48533.
  rewrite ?node_48534.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48536 (s : N.State) (i : N.Inputs) :
  R.v48536 (state s) (inputs i) = Zmod.unsigned (N.v48536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48536 s i)) at 1.
  unfold R.v48536, N.v48536.
  unfold R.v16463, N.v16463.
  rewrite ?node_48535.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48537 (s : N.State) (i : N.Inputs) :
  R.v48537 (state s) (inputs i) = Zmod.unsigned (N.v48537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48537 s i)) at 1.
  unfold R.v48537, N.v48537.
  rewrite ?node_16124.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48538 (s : N.State) (i : N.Inputs) :
  R.v48538 (state s) (inputs i) = Zmod.unsigned (N.v48538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48538 s i)) at 1.
  unfold R.v48538, N.v48538.
  unfold R.v6, N.v6.
  rewrite ?node_16143.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48539 (s : N.State) (i : N.Inputs) :
  R.v48539 (state s) (inputs i) = Zmod.unsigned (N.v48539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48539 s i)) at 1.
  unfold R.v48539, N.v48539.
  rewrite ?node_48537.
  rewrite ?node_48538.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48540 (s : N.State) (i : N.Inputs) :
  R.v48540 (state s) (inputs i) = Zmod.unsigned (N.v48540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48540 s i)) at 1.
  unfold R.v48540, N.v48540.
  rewrite ?node_48536.
  rewrite ?node_48539.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48541 (s : N.State) (i : N.Inputs) :
  R.v48541 (state s) (inputs i) = Zmod.unsigned (N.v48541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48541 s i)) at 1.
  unfold R.v48541, N.v48541.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48542 (s : N.State) (i : N.Inputs) :
  R.v48542 (state s) (inputs i) = Zmod.unsigned (N.v48542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48542 s i)) at 1.
  unfold R.v48542, N.v48542.
  rewrite ?node_16141.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48543 (s : N.State) (i : N.Inputs) :
  R.v48543 (state s) (inputs i) = Zmod.unsigned (N.v48543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48543 s i)) at 1.
  unfold R.v48543, N.v48543.
  unfold R.v6, N.v6.
  rewrite ?node_16137.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48544 (s : N.State) (i : N.Inputs) :
  R.v48544 (state s) (inputs i) = Zmod.unsigned (N.v48544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48544 s i)) at 1.
  unfold R.v48544, N.v48544.
  unfold R.v6, N.v6.
  rewrite ?node_16135.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48545 (s : N.State) (i : N.Inputs) :
  R.v48545 (state s) (inputs i) = Zmod.unsigned (N.v48545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48545 s i)) at 1.
  unfold R.v48545, N.v48545.
  rewrite ?node_48543.
  rewrite ?node_48544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48546 (s : N.State) (i : N.Inputs) :
  R.v48546 (state s) (inputs i) = Zmod.unsigned (N.v48546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48546 s i)) at 1.
  unfold R.v48546, N.v48546.
  unfold R.v16484, N.v16484.
  rewrite ?node_48545.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48547 (s : N.State) (i : N.Inputs) :
  R.v48547 (state s) (inputs i) = Zmod.unsigned (N.v48547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48547 s i)) at 1.
  unfold R.v48547, N.v48547.
  rewrite ?node_48542.
  rewrite ?node_48546.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48548 (s : N.State) (i : N.Inputs) :
  R.v48548 (state s) (inputs i) = Zmod.unsigned (N.v48548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48548 s i)) at 1.
  unfold R.v48548, N.v48548.
  unfold R.v6, N.v6.
  rewrite ?node_48547.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48549 (s : N.State) (i : N.Inputs) :
  R.v48549 (state s) (inputs i) = Zmod.unsigned (N.v48549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48549 s i)) at 1.
  unfold R.v48549, N.v48549.
  rewrite ?node_16142.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48550 (s : N.State) (i : N.Inputs) :
  R.v48550 (state s) (inputs i) = Zmod.unsigned (N.v48550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48550 s i)) at 1.
  unfold R.v48550, N.v48550.
  unfold R.v6, N.v6.
  rewrite ?node_16160.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48551 (s : N.State) (i : N.Inputs) :
  R.v48551 (state s) (inputs i) = Zmod.unsigned (N.v48551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48551 s i)) at 1.
  unfold R.v48551, N.v48551.
  rewrite ?node_48549.
  rewrite ?node_48550.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48552 (s : N.State) (i : N.Inputs) :
  R.v48552 (state s) (inputs i) = Zmod.unsigned (N.v48552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48552 s i)) at 1.
  unfold R.v48552, N.v48552.
  rewrite ?node_48548.
  rewrite ?node_48551.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48553 (s : N.State) (i : N.Inputs) :
  R.v48553 (state s) (inputs i) = Zmod.unsigned (N.v48553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48553 s i)) at 1.
  unfold R.v48553, N.v48553.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48554 (s : N.State) (i : N.Inputs) :
  R.v48554 (state s) (inputs i) = Zmod.unsigned (N.v48554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48554 s i)) at 1.
  unfold R.v48554, N.v48554.
  unfold R.v6, N.v6.
  rewrite ?node_16156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48555 (s : N.State) (i : N.Inputs) :
  R.v48555 (state s) (inputs i) = Zmod.unsigned (N.v48555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48555 s i)) at 1.
  unfold R.v48555, N.v48555.
  unfold R.v6, N.v6.
  rewrite ?node_16153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48556 (s : N.State) (i : N.Inputs) :
  R.v48556 (state s) (inputs i) = Zmod.unsigned (N.v48556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48556 s i)) at 1.
  unfold R.v48556, N.v48556.
  rewrite ?node_48554.
  rewrite ?node_48555.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48557 (s : N.State) (i : N.Inputs) :
  R.v48557 (state s) (inputs i) = Zmod.unsigned (N.v48557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48557 s i)) at 1.
  unfold R.v48557, N.v48557.
  unfold R.v16463, N.v16463.
  rewrite ?node_48556.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48558 (s : N.State) (i : N.Inputs) :
  R.v48558 (state s) (inputs i) = Zmod.unsigned (N.v48558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48558 s i)) at 1.
  unfold R.v48558, N.v48558.
  rewrite ?node_16157.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48559 (s : N.State) (i : N.Inputs) :
  R.v48559 (state s) (inputs i) = Zmod.unsigned (N.v48559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48559 s i)) at 1.
  unfold R.v48559, N.v48559.
  unfold R.v6, N.v6.
  rewrite ?node_16173.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48560 (s : N.State) (i : N.Inputs) :
  R.v48560 (state s) (inputs i) = Zmod.unsigned (N.v48560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48560 s i)) at 1.
  unfold R.v48560, N.v48560.
  rewrite ?node_48558.
  rewrite ?node_48559.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48561 (s : N.State) (i : N.Inputs) :
  R.v48561 (state s) (inputs i) = Zmod.unsigned (N.v48561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48561 s i)) at 1.
  unfold R.v48561, N.v48561.
  rewrite ?node_48557.
  rewrite ?node_48560.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48562 (s : N.State) (i : N.Inputs) :
  R.v48562 (state s) (inputs i) = Zmod.unsigned (N.v48562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48562 s i)) at 1.
  unfold R.v48562, N.v48562.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48563 (s : N.State) (i : N.Inputs) :
  R.v48563 (state s) (inputs i) = Zmod.unsigned (N.v48563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48563 s i)) at 1.
  unfold R.v48563, N.v48563.
  unfold R.v6, N.v6.
  rewrite ?node_16171.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48564 (s : N.State) (i : N.Inputs) :
  R.v48564 (state s) (inputs i) = Zmod.unsigned (N.v48564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48564 s i)) at 1.
  unfold R.v48564, N.v48564.
  unfold R.v6, N.v6.
  rewrite ?node_16169.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48565 (s : N.State) (i : N.Inputs) :
  R.v48565 (state s) (inputs i) = Zmod.unsigned (N.v48565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48565 s i)) at 1.
  unfold R.v48565, N.v48565.
  rewrite ?node_48563.
  rewrite ?node_48564.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48566 (s : N.State) (i : N.Inputs) :
  R.v48566 (state s) (inputs i) = Zmod.unsigned (N.v48566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48566 s i)) at 1.
  unfold R.v48566, N.v48566.
  unfold R.v16463, N.v16463.
  rewrite ?node_48565.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48567 (s : N.State) (i : N.Inputs) :
  R.v48567 (state s) (inputs i) = Zmod.unsigned (N.v48567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48567 s i)) at 1.
  unfold R.v48567, N.v48567.
  rewrite ?node_16172.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48568 (s : N.State) (i : N.Inputs) :
  R.v48568 (state s) (inputs i) = Zmod.unsigned (N.v48568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48568 s i)) at 1.
  unfold R.v48568, N.v48568.
  unfold R.v6, N.v6.
  rewrite ?node_16185.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48569 (s : N.State) (i : N.Inputs) :
  R.v48569 (state s) (inputs i) = Zmod.unsigned (N.v48569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48569 s i)) at 1.
  unfold R.v48569, N.v48569.
  rewrite ?node_48567.
  rewrite ?node_48568.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48570 (s : N.State) (i : N.Inputs) :
  R.v48570 (state s) (inputs i) = Zmod.unsigned (N.v48570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48570 s i)) at 1.
  unfold R.v48570, N.v48570.
  rewrite ?node_48566.
  rewrite ?node_48569.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48571 (s : N.State) (i : N.Inputs) :
  R.v48571 (state s) (inputs i) = Zmod.unsigned (N.v48571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48571 s i)) at 1.
  unfold R.v48571, N.v48571.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48572 (s : N.State) (i : N.Inputs) :
  R.v48572 (state s) (inputs i) = Zmod.unsigned (N.v48572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48572 s i)) at 1.
  unfold R.v48572, N.v48572.
  unfold R.v6, N.v6.
  rewrite ?node_16183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48573 (s : N.State) (i : N.Inputs) :
  R.v48573 (state s) (inputs i) = Zmod.unsigned (N.v48573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48573 s i)) at 1.
  unfold R.v48573, N.v48573.
  unfold R.v6, N.v6.
  rewrite ?node_16182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48574 (s : N.State) (i : N.Inputs) :
  R.v48574 (state s) (inputs i) = Zmod.unsigned (N.v48574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48574 s i)) at 1.
  unfold R.v48574, N.v48574.
  rewrite ?node_48572.
  rewrite ?node_48573.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48575 (s : N.State) (i : N.Inputs) :
  R.v48575 (state s) (inputs i) = Zmod.unsigned (N.v48575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48575 s i)) at 1.
  unfold R.v48575, N.v48575.
  unfold R.v16463, N.v16463.
  rewrite ?node_48574.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48576 (s : N.State) (i : N.Inputs) :
  R.v48576 (state s) (inputs i) = Zmod.unsigned (N.v48576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48576 s i)) at 1.
  unfold R.v48576, N.v48576.
  rewrite ?node_16184.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48577 (s : N.State) (i : N.Inputs) :
  R.v48577 (state s) (inputs i) = Zmod.unsigned (N.v48577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48577 s i)) at 1.
  unfold R.v48577, N.v48577.
  rewrite ?node_16182.
  rewrite ?node_16183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48578 (s : N.State) (i : N.Inputs) :
  R.v48578 (state s) (inputs i) = Zmod.unsigned (N.v48578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48578 s i)) at 1.
  unfold R.v48578, N.v48578.
  unfold R.v6, N.v6.
  unfold R.v16463, N.v16463.
  rewrite ?node_48577.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48579 (s : N.State) (i : N.Inputs) :
  R.v48579 (state s) (inputs i) = Zmod.unsigned (N.v48579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48579 s i)) at 1.
  unfold R.v48579, N.v48579.
  rewrite ?node_48576.
  rewrite ?node_48578.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48580 (s : N.State) (i : N.Inputs) :
  R.v48580 (state s) (inputs i) = Zmod.unsigned (N.v48580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48580 s i)) at 1.
  unfold R.v48580, N.v48580.
  rewrite ?node_48575.
  rewrite ?node_48579.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48581 (s : N.State) (i : N.Inputs) :
  R.v48581 (state s) (inputs i) = Zmod.unsigned (N.v48581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48581 s i)) at 1.
  unfold R.v48581, N.v48581.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48582 (s : N.State) (i : N.Inputs) :
  R.v48582 (state s) (inputs i) = Zmod.unsigned (N.v48582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48582 s i)) at 1.
  unfold R.v48582, N.v48582.
  unfold R.v6, N.v6.
  rewrite ?node_5111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48583 (s : N.State) (i : N.Inputs) :
  R.v48583 (state s) (inputs i) = Zmod.unsigned (N.v48583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48583 s i)) at 1.
  unfold R.v48583, N.v48583.
  unfold R.v6, N.v6.
  rewrite ?node_5110.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48584 (s : N.State) (i : N.Inputs) :
  R.v48584 (state s) (inputs i) = Zmod.unsigned (N.v48584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48584 s i)) at 1.
  unfold R.v48584, N.v48584.
  rewrite ?node_48582.
  rewrite ?node_48583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48585 (s : N.State) (i : N.Inputs) :
  R.v48585 (state s) (inputs i) = Zmod.unsigned (N.v48585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48585 s i)) at 1.
  unfold R.v48585, N.v48585.
  unfold R.v16463, N.v16463.
  rewrite ?node_48584.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48586 (s : N.State) (i : N.Inputs) :
  R.v48586 (state s) (inputs i) = Zmod.unsigned (N.v48586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48586 s i)) at 1.
  unfold R.v48586, N.v48586.
  rewrite ?node_5112.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48587 (s : N.State) (i : N.Inputs) :
  R.v48587 (state s) (inputs i) = Zmod.unsigned (N.v48587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48587 s i)) at 1.
  unfold R.v48587, N.v48587.
  unfold R.v6, N.v6.
  rewrite ?node_5122.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48588 (s : N.State) (i : N.Inputs) :
  R.v48588 (state s) (inputs i) = Zmod.unsigned (N.v48588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48588 s i)) at 1.
  unfold R.v48588, N.v48588.
  rewrite ?node_48586.
  rewrite ?node_48587.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48589 (s : N.State) (i : N.Inputs) :
  R.v48589 (state s) (inputs i) = Zmod.unsigned (N.v48589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48589 s i)) at 1.
  unfold R.v48589, N.v48589.
  rewrite ?node_48585.
  rewrite ?node_48588.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48590 (s : N.State) (i : N.Inputs) :
  R.v48590 (state s) (inputs i) = Zmod.unsigned (N.v48590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48590 s i)) at 1.
  unfold R.v48590, N.v48590.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48591 (s : N.State) (i : N.Inputs) :
  R.v48591 (state s) (inputs i) = Zmod.unsigned (N.v48591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48591 s i)) at 1.
  unfold R.v48591, N.v48591.
  unfold R.v6, N.v6.
  rewrite ?node_5120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48592 (s : N.State) (i : N.Inputs) :
  R.v48592 (state s) (inputs i) = Zmod.unsigned (N.v48592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48592 s i)) at 1.
  unfold R.v48592, N.v48592.
  unfold R.v6, N.v6.
  rewrite ?node_5119.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48593 (s : N.State) (i : N.Inputs) :
  R.v48593 (state s) (inputs i) = Zmod.unsigned (N.v48593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48593 s i)) at 1.
  unfold R.v48593, N.v48593.
  rewrite ?node_48591.
  rewrite ?node_48592.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48594 (s : N.State) (i : N.Inputs) :
  R.v48594 (state s) (inputs i) = Zmod.unsigned (N.v48594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48594 s i)) at 1.
  unfold R.v48594, N.v48594.
  unfold R.v16463, N.v16463.
  rewrite ?node_48593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48595 (s : N.State) (i : N.Inputs) :
  R.v48595 (state s) (inputs i) = Zmod.unsigned (N.v48595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48595 s i)) at 1.
  unfold R.v48595, N.v48595.
  rewrite ?node_5121.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48596 (s : N.State) (i : N.Inputs) :
  R.v48596 (state s) (inputs i) = Zmod.unsigned (N.v48596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48596 s i)) at 1.
  unfold R.v48596, N.v48596.
  unfold R.v6, N.v6.
  rewrite ?node_5134.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48597 (s : N.State) (i : N.Inputs) :
  R.v48597 (state s) (inputs i) = Zmod.unsigned (N.v48597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48597 s i)) at 1.
  unfold R.v48597, N.v48597.
  rewrite ?node_48595.
  rewrite ?node_48596.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48598 (s : N.State) (i : N.Inputs) :
  R.v48598 (state s) (inputs i) = Zmod.unsigned (N.v48598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48598 s i)) at 1.
  unfold R.v48598, N.v48598.
  rewrite ?node_48594.
  rewrite ?node_48597.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48599 (s : N.State) (i : N.Inputs) :
  R.v48599 (state s) (inputs i) = Zmod.unsigned (N.v48599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48599 s i)) at 1.
  unfold R.v48599, N.v48599.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48600 (s : N.State) (i : N.Inputs) :
  R.v48600 (state s) (inputs i) = Zmod.unsigned (N.v48600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48600 s i)) at 1.
  unfold R.v48600, N.v48600.
  unfold R.v6, N.v6.
  rewrite ?node_5132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48601 (s : N.State) (i : N.Inputs) :
  R.v48601 (state s) (inputs i) = Zmod.unsigned (N.v48601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48601 s i)) at 1.
  unfold R.v48601, N.v48601.
  unfold R.v6, N.v6.
  rewrite ?node_5131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48602 (s : N.State) (i : N.Inputs) :
  R.v48602 (state s) (inputs i) = Zmod.unsigned (N.v48602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48602 s i)) at 1.
  unfold R.v48602, N.v48602.
  rewrite ?node_48600.
  rewrite ?node_48601.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48603 (s : N.State) (i : N.Inputs) :
  R.v48603 (state s) (inputs i) = Zmod.unsigned (N.v48603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48603 s i)) at 1.
  unfold R.v48603, N.v48603.
  unfold R.v16463, N.v16463.
  rewrite ?node_48602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48604 (s : N.State) (i : N.Inputs) :
  R.v48604 (state s) (inputs i) = Zmod.unsigned (N.v48604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48604 s i)) at 1.
  unfold R.v48604, N.v48604.
  rewrite ?node_5133.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48605 (s : N.State) (i : N.Inputs) :
  R.v48605 (state s) (inputs i) = Zmod.unsigned (N.v48605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48605 s i)) at 1.
  unfold R.v48605, N.v48605.
  unfold R.v6, N.v6.
  rewrite ?node_5150.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48606 (s : N.State) (i : N.Inputs) :
  R.v48606 (state s) (inputs i) = Zmod.unsigned (N.v48606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48606 s i)) at 1.
  unfold R.v48606, N.v48606.
  rewrite ?node_48604.
  rewrite ?node_48605.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48607 (s : N.State) (i : N.Inputs) :
  R.v48607 (state s) (inputs i) = Zmod.unsigned (N.v48607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48607 s i)) at 1.
  unfold R.v48607, N.v48607.
  rewrite ?node_48603.
  rewrite ?node_48606.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48608 (s : N.State) (i : N.Inputs) :
  R.v48608 (state s) (inputs i) = Zmod.unsigned (N.v48608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48608 s i)) at 1.
  unfold R.v48608, N.v48608.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48609 (s : N.State) (i : N.Inputs) :
  R.v48609 (state s) (inputs i) = Zmod.unsigned (N.v48609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48609 s i)) at 1.
  unfold R.v48609, N.v48609.
  unfold R.v6, N.v6.
  rewrite ?node_5148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48610 (s : N.State) (i : N.Inputs) :
  R.v48610 (state s) (inputs i) = Zmod.unsigned (N.v48610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48610 s i)) at 1.
  unfold R.v48610, N.v48610.
  unfold R.v6, N.v6.
  rewrite ?node_5147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48611 (s : N.State) (i : N.Inputs) :
  R.v48611 (state s) (inputs i) = Zmod.unsigned (N.v48611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48611 s i)) at 1.
  unfold R.v48611, N.v48611.
  rewrite ?node_48609.
  rewrite ?node_48610.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48612 (s : N.State) (i : N.Inputs) :
  R.v48612 (state s) (inputs i) = Zmod.unsigned (N.v48612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48612 s i)) at 1.
  unfold R.v48612, N.v48612.
  unfold R.v16463, N.v16463.
  rewrite ?node_48611.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48613 (s : N.State) (i : N.Inputs) :
  R.v48613 (state s) (inputs i) = Zmod.unsigned (N.v48613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48613 s i)) at 1.
  unfold R.v48613, N.v48613.
  rewrite ?node_5149.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48614 (s : N.State) (i : N.Inputs) :
  R.v48614 (state s) (inputs i) = Zmod.unsigned (N.v48614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48614 s i)) at 1.
  unfold R.v48614, N.v48614.
  unfold R.v6, N.v6.
  rewrite ?node_5171.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48615 (s : N.State) (i : N.Inputs) :
  R.v48615 (state s) (inputs i) = Zmod.unsigned (N.v48615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48615 s i)) at 1.
  unfold R.v48615, N.v48615.
  rewrite ?node_48613.
  rewrite ?node_48614.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48616 (s : N.State) (i : N.Inputs) :
  R.v48616 (state s) (inputs i) = Zmod.unsigned (N.v48616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48616 s i)) at 1.
  unfold R.v48616, N.v48616.
  rewrite ?node_48612.
  rewrite ?node_48615.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48617 (s : N.State) (i : N.Inputs) :
  R.v48617 (state s) (inputs i) = Zmod.unsigned (N.v48617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48617 s i)) at 1.
  unfold R.v48617, N.v48617.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48618 (s : N.State) (i : N.Inputs) :
  R.v48618 (state s) (inputs i) = Zmod.unsigned (N.v48618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48618 s i)) at 1.
  unfold R.v48618, N.v48618.
  unfold R.v6, N.v6.
  rewrite ?node_5169.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48619 (s : N.State) (i : N.Inputs) :
  R.v48619 (state s) (inputs i) = Zmod.unsigned (N.v48619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48619 s i)) at 1.
  unfold R.v48619, N.v48619.
  unfold R.v6, N.v6.
  rewrite ?node_5168.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48620 (s : N.State) (i : N.Inputs) :
  R.v48620 (state s) (inputs i) = Zmod.unsigned (N.v48620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48620 s i)) at 1.
  unfold R.v48620, N.v48620.
  rewrite ?node_48618.
  rewrite ?node_48619.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48621 (s : N.State) (i : N.Inputs) :
  R.v48621 (state s) (inputs i) = Zmod.unsigned (N.v48621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48621 s i)) at 1.
  unfold R.v48621, N.v48621.
  unfold R.v16463, N.v16463.
  rewrite ?node_48620.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48622 (s : N.State) (i : N.Inputs) :
  R.v48622 (state s) (inputs i) = Zmod.unsigned (N.v48622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48622 s i)) at 1.
  unfold R.v48622, N.v48622.
  rewrite ?node_5170.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48623 (s : N.State) (i : N.Inputs) :
  R.v48623 (state s) (inputs i) = Zmod.unsigned (N.v48623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48623 s i)) at 1.
  unfold R.v48623, N.v48623.
  unfold R.v6, N.v6.
  rewrite ?node_5194.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48624 (s : N.State) (i : N.Inputs) :
  R.v48624 (state s) (inputs i) = Zmod.unsigned (N.v48624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48624 s i)) at 1.
  unfold R.v48624, N.v48624.
  rewrite ?node_48622.
  rewrite ?node_48623.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48625 (s : N.State) (i : N.Inputs) :
  R.v48625 (state s) (inputs i) = Zmod.unsigned (N.v48625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48625 s i)) at 1.
  unfold R.v48625, N.v48625.
  rewrite ?node_48621.
  rewrite ?node_48624.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48626 (s : N.State) (i : N.Inputs) :
  R.v48626 (state s) (inputs i) = Zmod.unsigned (N.v48626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48626 s i)) at 1.
  unfold R.v48626, N.v48626.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48627 (s : N.State) (i : N.Inputs) :
  R.v48627 (state s) (inputs i) = Zmod.unsigned (N.v48627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48627 s i)) at 1.
  unfold R.v48627, N.v48627.
  unfold R.v6, N.v6.
  rewrite ?node_5192.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48628 (s : N.State) (i : N.Inputs) :
  R.v48628 (state s) (inputs i) = Zmod.unsigned (N.v48628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48628 s i)) at 1.
  unfold R.v48628, N.v48628.
  unfold R.v6, N.v6.
  rewrite ?node_5189.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48629 (s : N.State) (i : N.Inputs) :
  R.v48629 (state s) (inputs i) = Zmod.unsigned (N.v48629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48629 s i)) at 1.
  unfold R.v48629, N.v48629.
  rewrite ?node_48627.
  rewrite ?node_48628.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48630 (s : N.State) (i : N.Inputs) :
  R.v48630 (state s) (inputs i) = Zmod.unsigned (N.v48630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48630 s i)) at 1.
  unfold R.v48630, N.v48630.
  unfold R.v16463, N.v16463.
  rewrite ?node_48629.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48631 (s : N.State) (i : N.Inputs) :
  R.v48631 (state s) (inputs i) = Zmod.unsigned (N.v48631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48631 s i)) at 1.
  unfold R.v48631, N.v48631.
  rewrite ?node_5193.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48632 (s : N.State) (i : N.Inputs) :
  R.v48632 (state s) (inputs i) = Zmod.unsigned (N.v48632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48632 s i)) at 1.
  unfold R.v48632, N.v48632.
  unfold R.v6, N.v6.
  rewrite ?node_5218.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48633 (s : N.State) (i : N.Inputs) :
  R.v48633 (state s) (inputs i) = Zmod.unsigned (N.v48633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48633 s i)) at 1.
  unfold R.v48633, N.v48633.
  rewrite ?node_48631.
  rewrite ?node_48632.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48634 (s : N.State) (i : N.Inputs) :
  R.v48634 (state s) (inputs i) = Zmod.unsigned (N.v48634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48634 s i)) at 1.
  unfold R.v48634, N.v48634.
  rewrite ?node_48630.
  rewrite ?node_48633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48635 (s : N.State) (i : N.Inputs) :
  R.v48635 (state s) (inputs i) = Zmod.unsigned (N.v48635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48635 s i)) at 1.
  unfold R.v48635, N.v48635.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48636 (s : N.State) (i : N.Inputs) :
  R.v48636 (state s) (inputs i) = Zmod.unsigned (N.v48636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48636 s i)) at 1.
  unfold R.v48636, N.v48636.
  unfold R.v6, N.v6.
  rewrite ?node_5216.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48637 (s : N.State) (i : N.Inputs) :
  R.v48637 (state s) (inputs i) = Zmod.unsigned (N.v48637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48637 s i)) at 1.
  unfold R.v48637, N.v48637.
  unfold R.v6, N.v6.
  rewrite ?node_5213.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48638 (s : N.State) (i : N.Inputs) :
  R.v48638 (state s) (inputs i) = Zmod.unsigned (N.v48638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48638 s i)) at 1.
  unfold R.v48638, N.v48638.
  rewrite ?node_48636.
  rewrite ?node_48637.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48639 (s : N.State) (i : N.Inputs) :
  R.v48639 (state s) (inputs i) = Zmod.unsigned (N.v48639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48639 s i)) at 1.
  unfold R.v48639, N.v48639.
  unfold R.v16463, N.v16463.
  rewrite ?node_48638.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48640 (s : N.State) (i : N.Inputs) :
  R.v48640 (state s) (inputs i) = Zmod.unsigned (N.v48640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48640 s i)) at 1.
  unfold R.v48640, N.v48640.
  rewrite ?node_5217.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48641 (s : N.State) (i : N.Inputs) :
  R.v48641 (state s) (inputs i) = Zmod.unsigned (N.v48641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48641 s i)) at 1.
  unfold R.v48641, N.v48641.
  unfold R.v6, N.v6.
  rewrite ?node_5244.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48642 (s : N.State) (i : N.Inputs) :
  R.v48642 (state s) (inputs i) = Zmod.unsigned (N.v48642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48642 s i)) at 1.
  unfold R.v48642, N.v48642.
  rewrite ?node_48640.
  rewrite ?node_48641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48643 (s : N.State) (i : N.Inputs) :
  R.v48643 (state s) (inputs i) = Zmod.unsigned (N.v48643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48643 s i)) at 1.
  unfold R.v48643, N.v48643.
  rewrite ?node_48639.
  rewrite ?node_48642.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48644 (s : N.State) (i : N.Inputs) :
  R.v48644 (state s) (inputs i) = Zmod.unsigned (N.v48644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48644 s i)) at 1.
  unfold R.v48644, N.v48644.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48645 (s : N.State) (i : N.Inputs) :
  R.v48645 (state s) (inputs i) = Zmod.unsigned (N.v48645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48645 s i)) at 1.
  unfold R.v48645, N.v48645.
  unfold R.v6, N.v6.
  rewrite ?node_5242.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48646 (s : N.State) (i : N.Inputs) :
  R.v48646 (state s) (inputs i) = Zmod.unsigned (N.v48646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48646 s i)) at 1.
  unfold R.v48646, N.v48646.
  unfold R.v6, N.v6.
  rewrite ?node_5239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48647 (s : N.State) (i : N.Inputs) :
  R.v48647 (state s) (inputs i) = Zmod.unsigned (N.v48647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48647 s i)) at 1.
  unfold R.v48647, N.v48647.
  rewrite ?node_48645.
  rewrite ?node_48646.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48648 (s : N.State) (i : N.Inputs) :
  R.v48648 (state s) (inputs i) = Zmod.unsigned (N.v48648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48648 s i)) at 1.
  unfold R.v48648, N.v48648.
  unfold R.v16463, N.v16463.
  rewrite ?node_48647.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48649 (s : N.State) (i : N.Inputs) :
  R.v48649 (state s) (inputs i) = Zmod.unsigned (N.v48649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48649 s i)) at 1.
  unfold R.v48649, N.v48649.
  rewrite ?node_5243.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48650 (s : N.State) (i : N.Inputs) :
  R.v48650 (state s) (inputs i) = Zmod.unsigned (N.v48650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48650 s i)) at 1.
  unfold R.v48650, N.v48650.
  unfold R.v6, N.v6.
  rewrite ?node_5273.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48651 (s : N.State) (i : N.Inputs) :
  R.v48651 (state s) (inputs i) = Zmod.unsigned (N.v48651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48651 s i)) at 1.
  unfold R.v48651, N.v48651.
  rewrite ?node_48649.
  rewrite ?node_48650.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48652 (s : N.State) (i : N.Inputs) :
  R.v48652 (state s) (inputs i) = Zmod.unsigned (N.v48652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48652 s i)) at 1.
  unfold R.v48652, N.v48652.
  rewrite ?node_48648.
  rewrite ?node_48651.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48653 (s : N.State) (i : N.Inputs) :
  R.v48653 (state s) (inputs i) = Zmod.unsigned (N.v48653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48653 s i)) at 1.
  unfold R.v48653, N.v48653.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48654 (s : N.State) (i : N.Inputs) :
  R.v48654 (state s) (inputs i) = Zmod.unsigned (N.v48654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48654 s i)) at 1.
  unfold R.v48654, N.v48654.
  unfold R.v6, N.v6.
  rewrite ?node_5271.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48655 (s : N.State) (i : N.Inputs) :
  R.v48655 (state s) (inputs i) = Zmod.unsigned (N.v48655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48655 s i)) at 1.
  unfold R.v48655, N.v48655.
  unfold R.v6, N.v6.
  rewrite ?node_5270.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48656 (s : N.State) (i : N.Inputs) :
  R.v48656 (state s) (inputs i) = Zmod.unsigned (N.v48656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48656 s i)) at 1.
  unfold R.v48656, N.v48656.
  rewrite ?node_48654.
  rewrite ?node_48655.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48657 (s : N.State) (i : N.Inputs) :
  R.v48657 (state s) (inputs i) = Zmod.unsigned (N.v48657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48657 s i)) at 1.
  unfold R.v48657, N.v48657.
  unfold R.v16463, N.v16463.
  rewrite ?node_48656.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48658 (s : N.State) (i : N.Inputs) :
  R.v48658 (state s) (inputs i) = Zmod.unsigned (N.v48658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48658 s i)) at 1.
  unfold R.v48658, N.v48658.
  rewrite ?node_5272.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48659 (s : N.State) (i : N.Inputs) :
  R.v48659 (state s) (inputs i) = Zmod.unsigned (N.v48659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48659 s i)) at 1.
  unfold R.v48659, N.v48659.
  unfold R.v6, N.v6.
  rewrite ?node_5306.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48660 (s : N.State) (i : N.Inputs) :
  R.v48660 (state s) (inputs i) = Zmod.unsigned (N.v48660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48660 s i)) at 1.
  unfold R.v48660, N.v48660.
  rewrite ?node_48658.
  rewrite ?node_48659.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48661 (s : N.State) (i : N.Inputs) :
  R.v48661 (state s) (inputs i) = Zmod.unsigned (N.v48661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48661 s i)) at 1.
  unfold R.v48661, N.v48661.
  rewrite ?node_48657.
  rewrite ?node_48660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48662 (s : N.State) (i : N.Inputs) :
  R.v48662 (state s) (inputs i) = Zmod.unsigned (N.v48662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48662 s i)) at 1.
  unfold R.v48662, N.v48662.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48663 (s : N.State) (i : N.Inputs) :
  R.v48663 (state s) (inputs i) = Zmod.unsigned (N.v48663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48663 s i)) at 1.
  unfold R.v48663, N.v48663.
  unfold R.v6, N.v6.
  rewrite ?node_5304.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48664 (s : N.State) (i : N.Inputs) :
  R.v48664 (state s) (inputs i) = Zmod.unsigned (N.v48664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48664 s i)) at 1.
  unfold R.v48664, N.v48664.
  unfold R.v6, N.v6.
  rewrite ?node_5301.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48665 (s : N.State) (i : N.Inputs) :
  R.v48665 (state s) (inputs i) = Zmod.unsigned (N.v48665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48665 s i)) at 1.
  unfold R.v48665, N.v48665.
  rewrite ?node_48663.
  rewrite ?node_48664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48666 (s : N.State) (i : N.Inputs) :
  R.v48666 (state s) (inputs i) = Zmod.unsigned (N.v48666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48666 s i)) at 1.
  unfold R.v48666, N.v48666.
  unfold R.v16463, N.v16463.
  rewrite ?node_48665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48667 (s : N.State) (i : N.Inputs) :
  R.v48667 (state s) (inputs i) = Zmod.unsigned (N.v48667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48667 s i)) at 1.
  unfold R.v48667, N.v48667.
  rewrite ?node_5305.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48668 (s : N.State) (i : N.Inputs) :
  R.v48668 (state s) (inputs i) = Zmod.unsigned (N.v48668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48668 s i)) at 1.
  unfold R.v48668, N.v48668.
  unfold R.v6, N.v6.
  rewrite ?node_5340.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48669 (s : N.State) (i : N.Inputs) :
  R.v48669 (state s) (inputs i) = Zmod.unsigned (N.v48669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48669 s i)) at 1.
  unfold R.v48669, N.v48669.
  rewrite ?node_48667.
  rewrite ?node_48668.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48670 (s : N.State) (i : N.Inputs) :
  R.v48670 (state s) (inputs i) = Zmod.unsigned (N.v48670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48670 s i)) at 1.
  unfold R.v48670, N.v48670.
  rewrite ?node_48666.
  rewrite ?node_48669.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48671 (s : N.State) (i : N.Inputs) :
  R.v48671 (state s) (inputs i) = Zmod.unsigned (N.v48671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48671 s i)) at 1.
  unfold R.v48671, N.v48671.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48672 (s : N.State) (i : N.Inputs) :
  R.v48672 (state s) (inputs i) = Zmod.unsigned (N.v48672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48672 s i)) at 1.
  unfold R.v48672, N.v48672.
  unfold R.v6, N.v6.
  rewrite ?node_5338.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48673 (s : N.State) (i : N.Inputs) :
  R.v48673 (state s) (inputs i) = Zmod.unsigned (N.v48673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48673 s i)) at 1.
  unfold R.v48673, N.v48673.
  unfold R.v6, N.v6.
  rewrite ?node_5335.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48674 (s : N.State) (i : N.Inputs) :
  R.v48674 (state s) (inputs i) = Zmod.unsigned (N.v48674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48674 s i)) at 1.
  unfold R.v48674, N.v48674.
  rewrite ?node_48672.
  rewrite ?node_48673.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48675 (s : N.State) (i : N.Inputs) :
  R.v48675 (state s) (inputs i) = Zmod.unsigned (N.v48675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48675 s i)) at 1.
  unfold R.v48675, N.v48675.
  unfold R.v16463, N.v16463.
  rewrite ?node_48674.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48676 (s : N.State) (i : N.Inputs) :
  R.v48676 (state s) (inputs i) = Zmod.unsigned (N.v48676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48676 s i)) at 1.
  unfold R.v48676, N.v48676.
  rewrite ?node_5339.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48677 (s : N.State) (i : N.Inputs) :
  R.v48677 (state s) (inputs i) = Zmod.unsigned (N.v48677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48677 s i)) at 1.
  unfold R.v48677, N.v48677.
  unfold R.v6, N.v6.
  rewrite ?node_5376.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48678 (s : N.State) (i : N.Inputs) :
  R.v48678 (state s) (inputs i) = Zmod.unsigned (N.v48678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48678 s i)) at 1.
  unfold R.v48678, N.v48678.
  rewrite ?node_48676.
  rewrite ?node_48677.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48679 (s : N.State) (i : N.Inputs) :
  R.v48679 (state s) (inputs i) = Zmod.unsigned (N.v48679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48679 s i)) at 1.
  unfold R.v48679, N.v48679.
  rewrite ?node_48675.
  rewrite ?node_48678.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48680 (s : N.State) (i : N.Inputs) :
  R.v48680 (state s) (inputs i) = Zmod.unsigned (N.v48680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48680 s i)) at 1.
  unfold R.v48680, N.v48680.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48681 (s : N.State) (i : N.Inputs) :
  R.v48681 (state s) (inputs i) = Zmod.unsigned (N.v48681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48681 s i)) at 1.
  unfold R.v48681, N.v48681.
  unfold R.v6, N.v6.
  rewrite ?node_5374.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48682 (s : N.State) (i : N.Inputs) :
  R.v48682 (state s) (inputs i) = Zmod.unsigned (N.v48682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48682 s i)) at 1.
  unfold R.v48682, N.v48682.
  unfold R.v6, N.v6.
  rewrite ?node_5371.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48683 (s : N.State) (i : N.Inputs) :
  R.v48683 (state s) (inputs i) = Zmod.unsigned (N.v48683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48683 s i)) at 1.
  unfold R.v48683, N.v48683.
  rewrite ?node_48681.
  rewrite ?node_48682.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48684 (s : N.State) (i : N.Inputs) :
  R.v48684 (state s) (inputs i) = Zmod.unsigned (N.v48684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48684 s i)) at 1.
  unfold R.v48684, N.v48684.
  unfold R.v16463, N.v16463.
  rewrite ?node_48683.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48685 (s : N.State) (i : N.Inputs) :
  R.v48685 (state s) (inputs i) = Zmod.unsigned (N.v48685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48685 s i)) at 1.
  unfold R.v48685, N.v48685.
  rewrite ?node_5375.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48686 (s : N.State) (i : N.Inputs) :
  R.v48686 (state s) (inputs i) = Zmod.unsigned (N.v48686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48686 s i)) at 1.
  unfold R.v48686, N.v48686.
  unfold R.v6, N.v6.
  rewrite ?node_5415.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48687 (s : N.State) (i : N.Inputs) :
  R.v48687 (state s) (inputs i) = Zmod.unsigned (N.v48687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48687 s i)) at 1.
  unfold R.v48687, N.v48687.
  rewrite ?node_48685.
  rewrite ?node_48686.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48688 (s : N.State) (i : N.Inputs) :
  R.v48688 (state s) (inputs i) = Zmod.unsigned (N.v48688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48688 s i)) at 1.
  unfold R.v48688, N.v48688.
  rewrite ?node_48684.
  rewrite ?node_48687.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48689 (s : N.State) (i : N.Inputs) :
  R.v48689 (state s) (inputs i) = Zmod.unsigned (N.v48689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48689 s i)) at 1.
  unfold R.v48689, N.v48689.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48690 (s : N.State) (i : N.Inputs) :
  R.v48690 (state s) (inputs i) = Zmod.unsigned (N.v48690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48690 s i)) at 1.
  unfold R.v48690, N.v48690.
  rewrite ?node_5413.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48691 (s : N.State) (i : N.Inputs) :
  R.v48691 (state s) (inputs i) = Zmod.unsigned (N.v48691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48691 s i)) at 1.
  unfold R.v48691, N.v48691.
  unfold R.v6, N.v6.
  rewrite ?node_5409.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48692 (s : N.State) (i : N.Inputs) :
  R.v48692 (state s) (inputs i) = Zmod.unsigned (N.v48692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48692 s i)) at 1.
  unfold R.v48692, N.v48692.
  unfold R.v6, N.v6.
  rewrite ?node_5406.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48693 (s : N.State) (i : N.Inputs) :
  R.v48693 (state s) (inputs i) = Zmod.unsigned (N.v48693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48693 s i)) at 1.
  unfold R.v48693, N.v48693.
  rewrite ?node_48691.
  rewrite ?node_48692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48694 (s : N.State) (i : N.Inputs) :
  R.v48694 (state s) (inputs i) = Zmod.unsigned (N.v48694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48694 s i)) at 1.
  unfold R.v48694, N.v48694.
  unfold R.v16484, N.v16484.
  rewrite ?node_48693.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48695 (s : N.State) (i : N.Inputs) :
  R.v48695 (state s) (inputs i) = Zmod.unsigned (N.v48695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48695 s i)) at 1.
  unfold R.v48695, N.v48695.
  rewrite ?node_48690.
  rewrite ?node_48694.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48696 (s : N.State) (i : N.Inputs) :
  R.v48696 (state s) (inputs i) = Zmod.unsigned (N.v48696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48696 s i)) at 1.
  unfold R.v48696, N.v48696.
  unfold R.v6, N.v6.
  rewrite ?node_48695.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48697 (s : N.State) (i : N.Inputs) :
  R.v48697 (state s) (inputs i) = Zmod.unsigned (N.v48697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48697 s i)) at 1.
  unfold R.v48697, N.v48697.
  rewrite ?node_5414.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48698 (s : N.State) (i : N.Inputs) :
  R.v48698 (state s) (inputs i) = Zmod.unsigned (N.v48698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48698 s i)) at 1.
  unfold R.v48698, N.v48698.
  unfold R.v6, N.v6.
  rewrite ?node_5456.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48699 (s : N.State) (i : N.Inputs) :
  R.v48699 (state s) (inputs i) = Zmod.unsigned (N.v48699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48699 s i)) at 1.
  unfold R.v48699, N.v48699.
  rewrite ?node_48697.
  rewrite ?node_48698.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48700 (s : N.State) (i : N.Inputs) :
  R.v48700 (state s) (inputs i) = Zmod.unsigned (N.v48700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48700 s i)) at 1.
  unfold R.v48700, N.v48700.
  rewrite ?node_48696.
  rewrite ?node_48699.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48701 (s : N.State) (i : N.Inputs) :
  R.v48701 (state s) (inputs i) = Zmod.unsigned (N.v48701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48701 s i)) at 1.
  unfold R.v48701, N.v48701.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48702 (s : N.State) (i : N.Inputs) :
  R.v48702 (state s) (inputs i) = Zmod.unsigned (N.v48702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48702 s i)) at 1.
  unfold R.v48702, N.v48702.
  rewrite ?node_5452.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48703 (s : N.State) (i : N.Inputs) :
  R.v48703 (state s) (inputs i) = Zmod.unsigned (N.v48703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48703 s i)) at 1.
  unfold R.v48703, N.v48703.
  unfold R.v6, N.v6.
  rewrite ?node_5448.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48704 (s : N.State) (i : N.Inputs) :
  R.v48704 (state s) (inputs i) = Zmod.unsigned (N.v48704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48704 s i)) at 1.
  unfold R.v48704, N.v48704.
  unfold R.v6, N.v6.
  rewrite ?node_5445.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48705 (s : N.State) (i : N.Inputs) :
  R.v48705 (state s) (inputs i) = Zmod.unsigned (N.v48705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48705 s i)) at 1.
  unfold R.v48705, N.v48705.
  rewrite ?node_48703.
  rewrite ?node_48704.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48706 (s : N.State) (i : N.Inputs) :
  R.v48706 (state s) (inputs i) = Zmod.unsigned (N.v48706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48706 s i)) at 1.
  unfold R.v48706, N.v48706.
  unfold R.v16484, N.v16484.
  rewrite ?node_48705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48707 (s : N.State) (i : N.Inputs) :
  R.v48707 (state s) (inputs i) = Zmod.unsigned (N.v48707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48707 s i)) at 1.
  unfold R.v48707, N.v48707.
  rewrite ?node_48702.
  rewrite ?node_48706.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48708 (s : N.State) (i : N.Inputs) :
  R.v48708 (state s) (inputs i) = Zmod.unsigned (N.v48708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48708 s i)) at 1.
  unfold R.v48708, N.v48708.
  unfold R.v6, N.v6.
  rewrite ?node_48707.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48709 (s : N.State) (i : N.Inputs) :
  R.v48709 (state s) (inputs i) = Zmod.unsigned (N.v48709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48709 s i)) at 1.
  unfold R.v48709, N.v48709.
  rewrite ?node_5453.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48710 (s : N.State) (i : N.Inputs) :
  R.v48710 (state s) (inputs i) = Zmod.unsigned (N.v48710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48710 s i)) at 1.
  unfold R.v48710, N.v48710.
  unfold R.v6, N.v6.
  rewrite ?node_5498.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48711 (s : N.State) (i : N.Inputs) :
  R.v48711 (state s) (inputs i) = Zmod.unsigned (N.v48711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48711 s i)) at 1.
  unfold R.v48711, N.v48711.
  rewrite ?node_48709.
  rewrite ?node_48710.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48712 (s : N.State) (i : N.Inputs) :
  R.v48712 (state s) (inputs i) = Zmod.unsigned (N.v48712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48712 s i)) at 1.
  unfold R.v48712, N.v48712.
  rewrite ?node_48708.
  rewrite ?node_48711.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48713 (s : N.State) (i : N.Inputs) :
  R.v48713 (state s) (inputs i) = Zmod.unsigned (N.v48713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48713 s i)) at 1.
  unfold R.v48713, N.v48713.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48714 (s : N.State) (i : N.Inputs) :
  R.v48714 (state s) (inputs i) = Zmod.unsigned (N.v48714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48714 s i)) at 1.
  unfold R.v48714, N.v48714.
  rewrite ?node_5494.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48715 (s : N.State) (i : N.Inputs) :
  R.v48715 (state s) (inputs i) = Zmod.unsigned (N.v48715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48715 s i)) at 1.
  unfold R.v48715, N.v48715.
  unfold R.v6, N.v6.
  rewrite ?node_5490.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48716 (s : N.State) (i : N.Inputs) :
  R.v48716 (state s) (inputs i) = Zmod.unsigned (N.v48716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48716 s i)) at 1.
  unfold R.v48716, N.v48716.
  unfold R.v6, N.v6.
  rewrite ?node_5487.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48717 (s : N.State) (i : N.Inputs) :
  R.v48717 (state s) (inputs i) = Zmod.unsigned (N.v48717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48717 s i)) at 1.
  unfold R.v48717, N.v48717.
  rewrite ?node_48715.
  rewrite ?node_48716.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48718 (s : N.State) (i : N.Inputs) :
  R.v48718 (state s) (inputs i) = Zmod.unsigned (N.v48718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48718 s i)) at 1.
  unfold R.v48718, N.v48718.
  unfold R.v16484, N.v16484.
  rewrite ?node_48717.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48719 (s : N.State) (i : N.Inputs) :
  R.v48719 (state s) (inputs i) = Zmod.unsigned (N.v48719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48719 s i)) at 1.
  unfold R.v48719, N.v48719.
  rewrite ?node_48714.
  rewrite ?node_48718.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48720 (s : N.State) (i : N.Inputs) :
  R.v48720 (state s) (inputs i) = Zmod.unsigned (N.v48720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48720 s i)) at 1.
  unfold R.v48720, N.v48720.
  unfold R.v6, N.v6.
  rewrite ?node_48719.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48721 (s : N.State) (i : N.Inputs) :
  R.v48721 (state s) (inputs i) = Zmod.unsigned (N.v48721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48721 s i)) at 1.
  unfold R.v48721, N.v48721.
  rewrite ?node_5495.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48722 (s : N.State) (i : N.Inputs) :
  R.v48722 (state s) (inputs i) = Zmod.unsigned (N.v48722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48722 s i)) at 1.
  unfold R.v48722, N.v48722.
  unfold R.v6, N.v6.
  rewrite ?node_5542.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48723 (s : N.State) (i : N.Inputs) :
  R.v48723 (state s) (inputs i) = Zmod.unsigned (N.v48723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48723 s i)) at 1.
  unfold R.v48723, N.v48723.
  rewrite ?node_48721.
  rewrite ?node_48722.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48724 (s : N.State) (i : N.Inputs) :
  R.v48724 (state s) (inputs i) = Zmod.unsigned (N.v48724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48724 s i)) at 1.
  unfold R.v48724, N.v48724.
  rewrite ?node_48720.
  rewrite ?node_48723.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48725 (s : N.State) (i : N.Inputs) :
  R.v48725 (state s) (inputs i) = Zmod.unsigned (N.v48725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48725 s i)) at 1.
  unfold R.v48725, N.v48725.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48726 (s : N.State) (i : N.Inputs) :
  R.v48726 (state s) (inputs i) = Zmod.unsigned (N.v48726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48726 s i)) at 1.
  unfold R.v48726, N.v48726.
  rewrite ?node_5538.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48727 (s : N.State) (i : N.Inputs) :
  R.v48727 (state s) (inputs i) = Zmod.unsigned (N.v48727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48727 s i)) at 1.
  unfold R.v48727, N.v48727.
  unfold R.v6, N.v6.
  rewrite ?node_5534.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48728 (s : N.State) (i : N.Inputs) :
  R.v48728 (state s) (inputs i) = Zmod.unsigned (N.v48728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48728 s i)) at 1.
  unfold R.v48728, N.v48728.
  unfold R.v6, N.v6.
  rewrite ?node_5529.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48729 (s : N.State) (i : N.Inputs) :
  R.v48729 (state s) (inputs i) = Zmod.unsigned (N.v48729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48729 s i)) at 1.
  unfold R.v48729, N.v48729.
  rewrite ?node_48727.
  rewrite ?node_48728.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48730 (s : N.State) (i : N.Inputs) :
  R.v48730 (state s) (inputs i) = Zmod.unsigned (N.v48730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48730 s i)) at 1.
  unfold R.v48730, N.v48730.
  unfold R.v16484, N.v16484.
  rewrite ?node_48729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48731 (s : N.State) (i : N.Inputs) :
  R.v48731 (state s) (inputs i) = Zmod.unsigned (N.v48731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48731 s i)) at 1.
  unfold R.v48731, N.v48731.
  rewrite ?node_48726.
  rewrite ?node_48730.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48732 (s : N.State) (i : N.Inputs) :
  R.v48732 (state s) (inputs i) = Zmod.unsigned (N.v48732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48732 s i)) at 1.
  unfold R.v48732, N.v48732.
  unfold R.v6, N.v6.
  rewrite ?node_48731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48733 (s : N.State) (i : N.Inputs) :
  R.v48733 (state s) (inputs i) = Zmod.unsigned (N.v48733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48733 s i)) at 1.
  unfold R.v48733, N.v48733.
  rewrite ?node_5539.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48734 (s : N.State) (i : N.Inputs) :
  R.v48734 (state s) (inputs i) = Zmod.unsigned (N.v48734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48734 s i)) at 1.
  unfold R.v48734, N.v48734.
  unfold R.v6, N.v6.
  rewrite ?node_5589.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48735 (s : N.State) (i : N.Inputs) :
  R.v48735 (state s) (inputs i) = Zmod.unsigned (N.v48735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48735 s i)) at 1.
  unfold R.v48735, N.v48735.
  rewrite ?node_48733.
  rewrite ?node_48734.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48736 (s : N.State) (i : N.Inputs) :
  R.v48736 (state s) (inputs i) = Zmod.unsigned (N.v48736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48736 s i)) at 1.
  unfold R.v48736, N.v48736.
  rewrite ?node_48732.
  rewrite ?node_48735.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48737 (s : N.State) (i : N.Inputs) :
  R.v48737 (state s) (inputs i) = Zmod.unsigned (N.v48737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48737 s i)) at 1.
  unfold R.v48737, N.v48737.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48738 (s : N.State) (i : N.Inputs) :
  R.v48738 (state s) (inputs i) = Zmod.unsigned (N.v48738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48738 s i)) at 1.
  unfold R.v48738, N.v48738.
  rewrite ?node_5585.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48739 (s : N.State) (i : N.Inputs) :
  R.v48739 (state s) (inputs i) = Zmod.unsigned (N.v48739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48739 s i)) at 1.
  unfold R.v48739, N.v48739.
  rewrite ?node_5583.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48740 (s : N.State) (i : N.Inputs) :
  R.v48740 (state s) (inputs i) = Zmod.unsigned (N.v48740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48740 s i)) at 1.
  unfold R.v48740, N.v48740.
  unfold R.v6, N.v6.
  rewrite ?node_5579.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48741 (s : N.State) (i : N.Inputs) :
  R.v48741 (state s) (inputs i) = Zmod.unsigned (N.v48741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48741 s i)) at 1.
  unfold R.v48741, N.v48741.
  unfold R.v6, N.v6.
  rewrite ?node_5574.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48742 (s : N.State) (i : N.Inputs) :
  R.v48742 (state s) (inputs i) = Zmod.unsigned (N.v48742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48742 s i)) at 1.
  unfold R.v48742, N.v48742.
  rewrite ?node_48740.
  rewrite ?node_48741.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48743 (s : N.State) (i : N.Inputs) :
  R.v48743 (state s) (inputs i) = Zmod.unsigned (N.v48743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48743 s i)) at 1.
  unfold R.v48743, N.v48743.
  unfold R.v16484, N.v16484.
  rewrite ?node_48742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48744 (s : N.State) (i : N.Inputs) :
  R.v48744 (state s) (inputs i) = Zmod.unsigned (N.v48744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48744 s i)) at 1.
  unfold R.v48744, N.v48744.
  rewrite ?node_48738.
  rewrite ?node_48739.
  rewrite ?node_48743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48745 (s : N.State) (i : N.Inputs) :
  R.v48745 (state s) (inputs i) = Zmod.unsigned (N.v48745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48745 s i)) at 1.
  unfold R.v48745, N.v48745.
  unfold R.v6, N.v6.
  rewrite ?node_48744.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48746 (s : N.State) (i : N.Inputs) :
  R.v48746 (state s) (inputs i) = Zmod.unsigned (N.v48746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48746 s i)) at 1.
  unfold R.v48746, N.v48746.
  rewrite ?node_5586.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48747 (s : N.State) (i : N.Inputs) :
  R.v48747 (state s) (inputs i) = Zmod.unsigned (N.v48747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48747 s i)) at 1.
  unfold R.v48747, N.v48747.
  unfold R.v6, N.v6.
  rewrite ?node_5638.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48748 (s : N.State) (i : N.Inputs) :
  R.v48748 (state s) (inputs i) = Zmod.unsigned (N.v48748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48748 s i)) at 1.
  unfold R.v48748, N.v48748.
  unfold R.v6, N.v6.
  rewrite ?node_5640.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48749 (s : N.State) (i : N.Inputs) :
  R.v48749 (state s) (inputs i) = Zmod.unsigned (N.v48749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48749 s i)) at 1.
  unfold R.v48749, N.v48749.
  rewrite ?node_48746.
  rewrite ?node_48747.
  rewrite ?node_48748.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48750 (s : N.State) (i : N.Inputs) :
  R.v48750 (state s) (inputs i) = Zmod.unsigned (N.v48750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48750 s i)) at 1.
  unfold R.v48750, N.v48750.
  rewrite ?node_48745.
  rewrite ?node_48749.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48751 (s : N.State) (i : N.Inputs) :
  R.v48751 (state s) (inputs i) = Zmod.unsigned (N.v48751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48751 s i)) at 1.
  unfold R.v48751, N.v48751.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48752 (s : N.State) (i : N.Inputs) :
  R.v48752 (state s) (inputs i) = Zmod.unsigned (N.v48752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48752 s i)) at 1.
  unfold R.v48752, N.v48752.
  rewrite ?node_5583.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48753 (s : N.State) (i : N.Inputs) :
  R.v48753 (state s) (inputs i) = Zmod.unsigned (N.v48753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48753 s i)) at 1.
  unfold R.v48753, N.v48753.
  unfold R.v6, N.v6.
  rewrite ?node_5579.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48754 (s : N.State) (i : N.Inputs) :
  R.v48754 (state s) (inputs i) = Zmod.unsigned (N.v48754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48754 s i)) at 1.
  unfold R.v48754, N.v48754.
  unfold R.v6, N.v6.
  rewrite ?node_5574.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48755 (s : N.State) (i : N.Inputs) :
  R.v48755 (state s) (inputs i) = Zmod.unsigned (N.v48755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48755 s i)) at 1.
  unfold R.v48755, N.v48755.
  rewrite ?node_48753.
  rewrite ?node_48754.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48756 (s : N.State) (i : N.Inputs) :
  R.v48756 (state s) (inputs i) = Zmod.unsigned (N.v48756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48756 s i)) at 1.
  unfold R.v48756, N.v48756.
  unfold R.v16484, N.v16484.
  rewrite ?node_48755.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48757 (s : N.State) (i : N.Inputs) :
  R.v48757 (state s) (inputs i) = Zmod.unsigned (N.v48757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48757 s i)) at 1.
  unfold R.v48757, N.v48757.
  rewrite ?node_48752.
  rewrite ?node_48756.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48758 (s : N.State) (i : N.Inputs) :
  R.v48758 (state s) (inputs i) = Zmod.unsigned (N.v48758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48758 s i)) at 1.
  unfold R.v48758, N.v48758.
  unfold R.v6, N.v6.
  rewrite ?node_48757.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48759 (s : N.State) (i : N.Inputs) :
  R.v48759 (state s) (inputs i) = Zmod.unsigned (N.v48759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48759 s i)) at 1.
  unfold R.v48759, N.v48759.
  rewrite ?node_5584.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48760 (s : N.State) (i : N.Inputs) :
  R.v48760 (state s) (inputs i) = Zmod.unsigned (N.v48760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48760 s i)) at 1.
  unfold R.v48760, N.v48760.
  unfold R.v6, N.v6.
  rewrite ?node_5638.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48761 (s : N.State) (i : N.Inputs) :
  R.v48761 (state s) (inputs i) = Zmod.unsigned (N.v48761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48761 s i)) at 1.
  unfold R.v48761, N.v48761.
  rewrite ?node_48759.
  rewrite ?node_48760.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48762 (s : N.State) (i : N.Inputs) :
  R.v48762 (state s) (inputs i) = Zmod.unsigned (N.v48762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48762 s i)) at 1.
  unfold R.v48762, N.v48762.
  rewrite ?node_48758.
  rewrite ?node_48761.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48763 (s : N.State) (i : N.Inputs) :
  R.v48763 (state s) (inputs i) = Zmod.unsigned (N.v48763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48763 s i)) at 1.
  unfold R.v48763, N.v48763.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48764 (s : N.State) (i : N.Inputs) :
  R.v48764 (state s) (inputs i) = Zmod.unsigned (N.v48764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48764 s i)) at 1.
  unfold R.v48764, N.v48764.
  unfold R.v6, N.v6.
  rewrite ?node_5585.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48765 (s : N.State) (i : N.Inputs) :
  R.v48765 (state s) (inputs i) = Zmod.unsigned (N.v48765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48765 s i)) at 1.
  unfold R.v48765, N.v48765.
  unfold R.v6, N.v6.
  rewrite ?node_5584.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48766 (s : N.State) (i : N.Inputs) :
  R.v48766 (state s) (inputs i) = Zmod.unsigned (N.v48766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48766 s i)) at 1.
  unfold R.v48766, N.v48766.
  rewrite ?node_48764.
  rewrite ?node_48765.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48767 (s : N.State) (i : N.Inputs) :
  R.v48767 (state s) (inputs i) = Zmod.unsigned (N.v48767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48767 s i)) at 1.
  unfold R.v48767, N.v48767.
  unfold R.v16463, N.v16463.
  rewrite ?node_48766.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48768 (s : N.State) (i : N.Inputs) :
  R.v48768 (state s) (inputs i) = Zmod.unsigned (N.v48768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48768 s i)) at 1.
  unfold R.v48768, N.v48768.
  rewrite ?node_5586.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48769 (s : N.State) (i : N.Inputs) :
  R.v48769 (state s) (inputs i) = Zmod.unsigned (N.v48769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48769 s i)) at 1.
  unfold R.v48769, N.v48769.
  unfold R.v6, N.v6.
  rewrite ?node_5640.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48770 (s : N.State) (i : N.Inputs) :
  R.v48770 (state s) (inputs i) = Zmod.unsigned (N.v48770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48770 s i)) at 1.
  unfold R.v48770, N.v48770.
  rewrite ?node_48768.
  rewrite ?node_48769.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48771 (s : N.State) (i : N.Inputs) :
  R.v48771 (state s) (inputs i) = Zmod.unsigned (N.v48771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48771 s i)) at 1.
  unfold R.v48771, N.v48771.
  rewrite ?node_48767.
  rewrite ?node_48770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48772 (s : N.State) (i : N.Inputs) :
  R.v48772 (state s) (inputs i) = Zmod.unsigned (N.v48772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48772 s i)) at 1.
  unfold R.v48772, N.v48772.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48773 (s : N.State) (i : N.Inputs) :
  R.v48773 (state s) (inputs i) = Zmod.unsigned (N.v48773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48773 s i)) at 1.
  unfold R.v48773, N.v48773.
  rewrite ?node_5638.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48774 (s : N.State) (i : N.Inputs) :
  R.v48774 (state s) (inputs i) = Zmod.unsigned (N.v48774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48774 s i)) at 1.
  unfold R.v48774, N.v48774.
  rewrite ?node_5634.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48775 (s : N.State) (i : N.Inputs) :
  R.v48775 (state s) (inputs i) = Zmod.unsigned (N.v48775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48775 s i)) at 1.
  unfold R.v48775, N.v48775.
  rewrite ?node_5632.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48776 (s : N.State) (i : N.Inputs) :
  R.v48776 (state s) (inputs i) = Zmod.unsigned (N.v48776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48776 s i)) at 1.
  unfold R.v48776, N.v48776.
  unfold R.v6, N.v6.
  rewrite ?node_5628.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48777 (s : N.State) (i : N.Inputs) :
  R.v48777 (state s) (inputs i) = Zmod.unsigned (N.v48777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48777 s i)) at 1.
  unfold R.v48777, N.v48777.
  unfold R.v6, N.v6.
  rewrite ?node_5621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48778 (s : N.State) (i : N.Inputs) :
  R.v48778 (state s) (inputs i) = Zmod.unsigned (N.v48778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48778 s i)) at 1.
  unfold R.v48778, N.v48778.
  rewrite ?node_48776.
  rewrite ?node_48777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48779 (s : N.State) (i : N.Inputs) :
  R.v48779 (state s) (inputs i) = Zmod.unsigned (N.v48779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48779 s i)) at 1.
  unfold R.v48779, N.v48779.
  unfold R.v16484, N.v16484.
  rewrite ?node_48778.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48780 (s : N.State) (i : N.Inputs) :
  R.v48780 (state s) (inputs i) = Zmod.unsigned (N.v48780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48780 s i)) at 1.
  unfold R.v48780, N.v48780.
  rewrite ?node_48773.
  rewrite ?node_48774.
  rewrite ?node_48775.
  rewrite ?node_48779.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48781 (s : N.State) (i : N.Inputs) :
  R.v48781 (state s) (inputs i) = Zmod.unsigned (N.v48781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48781 s i)) at 1.
  unfold R.v48781, N.v48781.
  unfold R.v6, N.v6.
  rewrite ?node_48780.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48782 (s : N.State) (i : N.Inputs) :
  R.v48782 (state s) (inputs i) = Zmod.unsigned (N.v48782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48782 s i)) at 1.
  unfold R.v48782, N.v48782.
  rewrite ?node_5639.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48783 (s : N.State) (i : N.Inputs) :
  R.v48783 (state s) (inputs i) = Zmod.unsigned (N.v48783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48783 s i)) at 1.
  unfold R.v48783, N.v48783.
  unfold R.v6, N.v6.
  rewrite ?node_5690.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48784 (s : N.State) (i : N.Inputs) :
  R.v48784 (state s) (inputs i) = Zmod.unsigned (N.v48784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48784 s i)) at 1.
  unfold R.v48784, N.v48784.
  unfold R.v6, N.v6.
  rewrite ?node_5694.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48785 (s : N.State) (i : N.Inputs) :
  R.v48785 (state s) (inputs i) = Zmod.unsigned (N.v48785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48785 s i)) at 1.
  unfold R.v48785, N.v48785.
  rewrite ?node_48782.
  rewrite ?node_48783.
  rewrite ?node_48784.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48786 (s : N.State) (i : N.Inputs) :
  R.v48786 (state s) (inputs i) = Zmod.unsigned (N.v48786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48786 s i)) at 1.
  unfold R.v48786, N.v48786.
  rewrite ?node_48781.
  rewrite ?node_48785.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48787 (s : N.State) (i : N.Inputs) :
  R.v48787 (state s) (inputs i) = Zmod.unsigned (N.v48787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48787 s i)) at 1.
  unfold R.v48787, N.v48787.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48788 (s : N.State) (i : N.Inputs) :
  R.v48788 (state s) (inputs i) = Zmod.unsigned (N.v48788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48788 s i)) at 1.
  unfold R.v48788, N.v48788.
  rewrite ?node_5632.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48789 (s : N.State) (i : N.Inputs) :
  R.v48789 (state s) (inputs i) = Zmod.unsigned (N.v48789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48789 s i)) at 1.
  unfold R.v48789, N.v48789.
  unfold R.v6, N.v6.
  rewrite ?node_5628.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48790 (s : N.State) (i : N.Inputs) :
  R.v48790 (state s) (inputs i) = Zmod.unsigned (N.v48790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48790 s i)) at 1.
  unfold R.v48790, N.v48790.
  unfold R.v6, N.v6.
  rewrite ?node_5621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48791 (s : N.State) (i : N.Inputs) :
  R.v48791 (state s) (inputs i) = Zmod.unsigned (N.v48791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48791 s i)) at 1.
  unfold R.v48791, N.v48791.
  rewrite ?node_48789.
  rewrite ?node_48790.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48792 (s : N.State) (i : N.Inputs) :
  R.v48792 (state s) (inputs i) = Zmod.unsigned (N.v48792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48792 s i)) at 1.
  unfold R.v48792, N.v48792.
  unfold R.v16484, N.v16484.
  rewrite ?node_48791.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48793 (s : N.State) (i : N.Inputs) :
  R.v48793 (state s) (inputs i) = Zmod.unsigned (N.v48793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48793 s i)) at 1.
  unfold R.v48793, N.v48793.
  rewrite ?node_48788.
  rewrite ?node_48792.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48794 (s : N.State) (i : N.Inputs) :
  R.v48794 (state s) (inputs i) = Zmod.unsigned (N.v48794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48794 s i)) at 1.
  unfold R.v48794, N.v48794.
  unfold R.v6, N.v6.
  rewrite ?node_48793.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48795 (s : N.State) (i : N.Inputs) :
  R.v48795 (state s) (inputs i) = Zmod.unsigned (N.v48795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48795 s i)) at 1.
  unfold R.v48795, N.v48795.
  rewrite ?node_5633.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48796 (s : N.State) (i : N.Inputs) :
  R.v48796 (state s) (inputs i) = Zmod.unsigned (N.v48796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48796 s i)) at 1.
  unfold R.v48796, N.v48796.
  unfold R.v6, N.v6.
  rewrite ?node_5690.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48797 (s : N.State) (i : N.Inputs) :
  R.v48797 (state s) (inputs i) = Zmod.unsigned (N.v48797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48797 s i)) at 1.
  unfold R.v48797, N.v48797.
  rewrite ?node_48795.
  rewrite ?node_48796.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48798 (s : N.State) (i : N.Inputs) :
  R.v48798 (state s) (inputs i) = Zmod.unsigned (N.v48798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48798 s i)) at 1.
  unfold R.v48798, N.v48798.
  rewrite ?node_48794.
  rewrite ?node_48797.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48799 (s : N.State) (i : N.Inputs) :
  R.v48799 (state s) (inputs i) = Zmod.unsigned (N.v48799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48799 s i)) at 1.
  unfold R.v48799, N.v48799.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48800 (s : N.State) (i : N.Inputs) :
  R.v48800 (state s) (inputs i) = Zmod.unsigned (N.v48800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48800 s i)) at 1.
  unfold R.v48800, N.v48800.
  rewrite ?node_5638.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48801 (s : N.State) (i : N.Inputs) :
  R.v48801 (state s) (inputs i) = Zmod.unsigned (N.v48801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48801 s i)) at 1.
  unfold R.v48801, N.v48801.
  unfold R.v6, N.v6.
  rewrite ?node_5634.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48802 (s : N.State) (i : N.Inputs) :
  R.v48802 (state s) (inputs i) = Zmod.unsigned (N.v48802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48802 s i)) at 1.
  unfold R.v48802, N.v48802.
  unfold R.v6, N.v6.
  rewrite ?node_5633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48803 (s : N.State) (i : N.Inputs) :
  R.v48803 (state s) (inputs i) = Zmod.unsigned (N.v48803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48803 s i)) at 1.
  unfold R.v48803, N.v48803.
  rewrite ?node_48801.
  rewrite ?node_48802.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48804 (s : N.State) (i : N.Inputs) :
  R.v48804 (state s) (inputs i) = Zmod.unsigned (N.v48804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48804 s i)) at 1.
  unfold R.v48804, N.v48804.
  unfold R.v16484, N.v16484.
  rewrite ?node_48803.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48805 (s : N.State) (i : N.Inputs) :
  R.v48805 (state s) (inputs i) = Zmod.unsigned (N.v48805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48805 s i)) at 1.
  unfold R.v48805, N.v48805.
  rewrite ?node_48800.
  rewrite ?node_48804.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48806 (s : N.State) (i : N.Inputs) :
  R.v48806 (state s) (inputs i) = Zmod.unsigned (N.v48806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48806 s i)) at 1.
  unfold R.v48806, N.v48806.
  unfold R.v6, N.v6.
  rewrite ?node_48805.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48807 (s : N.State) (i : N.Inputs) :
  R.v48807 (state s) (inputs i) = Zmod.unsigned (N.v48807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48807 s i)) at 1.
  unfold R.v48807, N.v48807.
  rewrite ?node_5639.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48808 (s : N.State) (i : N.Inputs) :
  R.v48808 (state s) (inputs i) = Zmod.unsigned (N.v48808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48808 s i)) at 1.
  unfold R.v48808, N.v48808.
  unfold R.v6, N.v6.
  rewrite ?node_5694.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48809 (s : N.State) (i : N.Inputs) :
  R.v48809 (state s) (inputs i) = Zmod.unsigned (N.v48809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48809 s i)) at 1.
  unfold R.v48809, N.v48809.
  rewrite ?node_48807.
  rewrite ?node_48808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48810 (s : N.State) (i : N.Inputs) :
  R.v48810 (state s) (inputs i) = Zmod.unsigned (N.v48810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48810 s i)) at 1.
  unfold R.v48810, N.v48810.
  rewrite ?node_48806.
  rewrite ?node_48809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48811 (s : N.State) (i : N.Inputs) :
  R.v48811 (state s) (inputs i) = Zmod.unsigned (N.v48811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48811 s i)) at 1.
  unfold R.v48811, N.v48811.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48812 (s : N.State) (i : N.Inputs) :
  R.v48812 (state s) (inputs i) = Zmod.unsigned (N.v48812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48812 s i)) at 1.
  unfold R.v48812, N.v48812.
  rewrite ?node_5690.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48813 (s : N.State) (i : N.Inputs) :
  R.v48813 (state s) (inputs i) = Zmod.unsigned (N.v48813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48813 s i)) at 1.
  unfold R.v48813, N.v48813.
  rewrite ?node_5686.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48814 (s : N.State) (i : N.Inputs) :
  R.v48814 (state s) (inputs i) = Zmod.unsigned (N.v48814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48814 s i)) at 1.
  unfold R.v48814, N.v48814.
  rewrite ?node_5684.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48815 (s : N.State) (i : N.Inputs) :
  R.v48815 (state s) (inputs i) = Zmod.unsigned (N.v48815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48815 s i)) at 1.
  unfold R.v48815, N.v48815.
  unfold R.v6, N.v6.
  rewrite ?node_5680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48816 (s : N.State) (i : N.Inputs) :
  R.v48816 (state s) (inputs i) = Zmod.unsigned (N.v48816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48816 s i)) at 1.
  unfold R.v48816, N.v48816.
  unfold R.v6, N.v6.
  rewrite ?node_5673.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48817 (s : N.State) (i : N.Inputs) :
  R.v48817 (state s) (inputs i) = Zmod.unsigned (N.v48817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48817 s i)) at 1.
  unfold R.v48817, N.v48817.
  rewrite ?node_48815.
  rewrite ?node_48816.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48818 (s : N.State) (i : N.Inputs) :
  R.v48818 (state s) (inputs i) = Zmod.unsigned (N.v48818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48818 s i)) at 1.
  unfold R.v48818, N.v48818.
  unfold R.v16484, N.v16484.
  rewrite ?node_48817.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48819 (s : N.State) (i : N.Inputs) :
  R.v48819 (state s) (inputs i) = Zmod.unsigned (N.v48819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48819 s i)) at 1.
  unfold R.v48819, N.v48819.
  rewrite ?node_48812.
  rewrite ?node_48813.
  rewrite ?node_48814.
  rewrite ?node_48818.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48820 (s : N.State) (i : N.Inputs) :
  R.v48820 (state s) (inputs i) = Zmod.unsigned (N.v48820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48820 s i)) at 1.
  unfold R.v48820, N.v48820.
  unfold R.v6, N.v6.
  rewrite ?node_48819.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48821 (s : N.State) (i : N.Inputs) :
  R.v48821 (state s) (inputs i) = Zmod.unsigned (N.v48821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48821 s i)) at 1.
  unfold R.v48821, N.v48821.
  rewrite ?node_5691.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48822 (s : N.State) (i : N.Inputs) :
  R.v48822 (state s) (inputs i) = Zmod.unsigned (N.v48822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48822 s i)) at 1.
  unfold R.v48822, N.v48822.
  unfold R.v6, N.v6.
  rewrite ?node_5746.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48823 (s : N.State) (i : N.Inputs) :
  R.v48823 (state s) (inputs i) = Zmod.unsigned (N.v48823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48823 s i)) at 1.
  unfold R.v48823, N.v48823.
  unfold R.v6, N.v6.
  rewrite ?node_5750.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48824 (s : N.State) (i : N.Inputs) :
  R.v48824 (state s) (inputs i) = Zmod.unsigned (N.v48824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48824 s i)) at 1.
  unfold R.v48824, N.v48824.
  rewrite ?node_48821.
  rewrite ?node_48822.
  rewrite ?node_48823.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48825 (s : N.State) (i : N.Inputs) :
  R.v48825 (state s) (inputs i) = Zmod.unsigned (N.v48825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48825 s i)) at 1.
  unfold R.v48825, N.v48825.
  rewrite ?node_48820.
  rewrite ?node_48824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48826 (s : N.State) (i : N.Inputs) :
  R.v48826 (state s) (inputs i) = Zmod.unsigned (N.v48826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48826 s i)) at 1.
  unfold R.v48826, N.v48826.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48827 (s : N.State) (i : N.Inputs) :
  R.v48827 (state s) (inputs i) = Zmod.unsigned (N.v48827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48827 s i)) at 1.
  unfold R.v48827, N.v48827.
  rewrite ?node_5684.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48828 (s : N.State) (i : N.Inputs) :
  R.v48828 (state s) (inputs i) = Zmod.unsigned (N.v48828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48828 s i)) at 1.
  unfold R.v48828, N.v48828.
  unfold R.v6, N.v6.
  rewrite ?node_5680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48829 (s : N.State) (i : N.Inputs) :
  R.v48829 (state s) (inputs i) = Zmod.unsigned (N.v48829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48829 s i)) at 1.
  unfold R.v48829, N.v48829.
  unfold R.v6, N.v6.
  rewrite ?node_5673.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48830 (s : N.State) (i : N.Inputs) :
  R.v48830 (state s) (inputs i) = Zmod.unsigned (N.v48830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48830 s i)) at 1.
  unfold R.v48830, N.v48830.
  rewrite ?node_48828.
  rewrite ?node_48829.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48831 (s : N.State) (i : N.Inputs) :
  R.v48831 (state s) (inputs i) = Zmod.unsigned (N.v48831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48831 s i)) at 1.
  unfold R.v48831, N.v48831.
  unfold R.v16484, N.v16484.
  rewrite ?node_48830.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48832 (s : N.State) (i : N.Inputs) :
  R.v48832 (state s) (inputs i) = Zmod.unsigned (N.v48832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48832 s i)) at 1.
  unfold R.v48832, N.v48832.
  rewrite ?node_48827.
  rewrite ?node_48831.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48833 (s : N.State) (i : N.Inputs) :
  R.v48833 (state s) (inputs i) = Zmod.unsigned (N.v48833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48833 s i)) at 1.
  unfold R.v48833, N.v48833.
  unfold R.v6, N.v6.
  rewrite ?node_48832.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48834 (s : N.State) (i : N.Inputs) :
  R.v48834 (state s) (inputs i) = Zmod.unsigned (N.v48834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48834 s i)) at 1.
  unfold R.v48834, N.v48834.
  rewrite ?node_5685.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48835 (s : N.State) (i : N.Inputs) :
  R.v48835 (state s) (inputs i) = Zmod.unsigned (N.v48835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48835 s i)) at 1.
  unfold R.v48835, N.v48835.
  unfold R.v6, N.v6.
  rewrite ?node_5746.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48836 (s : N.State) (i : N.Inputs) :
  R.v48836 (state s) (inputs i) = Zmod.unsigned (N.v48836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48836 s i)) at 1.
  unfold R.v48836, N.v48836.
  rewrite ?node_48834.
  rewrite ?node_48835.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48837 (s : N.State) (i : N.Inputs) :
  R.v48837 (state s) (inputs i) = Zmod.unsigned (N.v48837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48837 s i)) at 1.
  unfold R.v48837, N.v48837.
  rewrite ?node_48833.
  rewrite ?node_48836.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48838 (s : N.State) (i : N.Inputs) :
  R.v48838 (state s) (inputs i) = Zmod.unsigned (N.v48838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48838 s i)) at 1.
  unfold R.v48838, N.v48838.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48839 (s : N.State) (i : N.Inputs) :
  R.v48839 (state s) (inputs i) = Zmod.unsigned (N.v48839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48839 s i)) at 1.
  unfold R.v48839, N.v48839.
  rewrite ?node_5690.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48840 (s : N.State) (i : N.Inputs) :
  R.v48840 (state s) (inputs i) = Zmod.unsigned (N.v48840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48840 s i)) at 1.
  unfold R.v48840, N.v48840.
  unfold R.v6, N.v6.
  rewrite ?node_5686.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48841 (s : N.State) (i : N.Inputs) :
  R.v48841 (state s) (inputs i) = Zmod.unsigned (N.v48841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48841 s i)) at 1.
  unfold R.v48841, N.v48841.
  unfold R.v6, N.v6.
  rewrite ?node_5685.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48842 (s : N.State) (i : N.Inputs) :
  R.v48842 (state s) (inputs i) = Zmod.unsigned (N.v48842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48842 s i)) at 1.
  unfold R.v48842, N.v48842.
  rewrite ?node_48840.
  rewrite ?node_48841.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48843 (s : N.State) (i : N.Inputs) :
  R.v48843 (state s) (inputs i) = Zmod.unsigned (N.v48843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48843 s i)) at 1.
  unfold R.v48843, N.v48843.
  unfold R.v16484, N.v16484.
  rewrite ?node_48842.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48844 (s : N.State) (i : N.Inputs) :
  R.v48844 (state s) (inputs i) = Zmod.unsigned (N.v48844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48844 s i)) at 1.
  unfold R.v48844, N.v48844.
  rewrite ?node_48839.
  rewrite ?node_48843.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48845 (s : N.State) (i : N.Inputs) :
  R.v48845 (state s) (inputs i) = Zmod.unsigned (N.v48845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48845 s i)) at 1.
  unfold R.v48845, N.v48845.
  unfold R.v6, N.v6.
  rewrite ?node_48844.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48846 (s : N.State) (i : N.Inputs) :
  R.v48846 (state s) (inputs i) = Zmod.unsigned (N.v48846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48846 s i)) at 1.
  unfold R.v48846, N.v48846.
  rewrite ?node_5691.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48847 (s : N.State) (i : N.Inputs) :
  R.v48847 (state s) (inputs i) = Zmod.unsigned (N.v48847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48847 s i)) at 1.
  unfold R.v48847, N.v48847.
  unfold R.v6, N.v6.
  rewrite ?node_5750.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48848 (s : N.State) (i : N.Inputs) :
  R.v48848 (state s) (inputs i) = Zmod.unsigned (N.v48848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48848 s i)) at 1.
  unfold R.v48848, N.v48848.
  rewrite ?node_48846.
  rewrite ?node_48847.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48849 (s : N.State) (i : N.Inputs) :
  R.v48849 (state s) (inputs i) = Zmod.unsigned (N.v48849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48849 s i)) at 1.
  unfold R.v48849, N.v48849.
  rewrite ?node_48845.
  rewrite ?node_48848.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48850 (s : N.State) (i : N.Inputs) :
  R.v48850 (state s) (inputs i) = Zmod.unsigned (N.v48850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48850 s i)) at 1.
  unfold R.v48850, N.v48850.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48851 (s : N.State) (i : N.Inputs) :
  R.v48851 (state s) (inputs i) = Zmod.unsigned (N.v48851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48851 s i)) at 1.
  unfold R.v48851, N.v48851.
  rewrite ?node_5746.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48852 (s : N.State) (i : N.Inputs) :
  R.v48852 (state s) (inputs i) = Zmod.unsigned (N.v48852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48852 s i)) at 1.
  unfold R.v48852, N.v48852.
  rewrite ?node_5742.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48853 (s : N.State) (i : N.Inputs) :
  R.v48853 (state s) (inputs i) = Zmod.unsigned (N.v48853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48853 s i)) at 1.
  unfold R.v48853, N.v48853.
  rewrite ?node_5740.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48854 (s : N.State) (i : N.Inputs) :
  R.v48854 (state s) (inputs i) = Zmod.unsigned (N.v48854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48854 s i)) at 1.
  unfold R.v48854, N.v48854.
  unfold R.v6, N.v6.
  rewrite ?node_5736.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48855 (s : N.State) (i : N.Inputs) :
  R.v48855 (state s) (inputs i) = Zmod.unsigned (N.v48855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48855 s i)) at 1.
  unfold R.v48855, N.v48855.
  unfold R.v6, N.v6.
  rewrite ?node_5731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48856 (s : N.State) (i : N.Inputs) :
  R.v48856 (state s) (inputs i) = Zmod.unsigned (N.v48856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48856 s i)) at 1.
  unfold R.v48856, N.v48856.
  rewrite ?node_48854.
  rewrite ?node_48855.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48857 (s : N.State) (i : N.Inputs) :
  R.v48857 (state s) (inputs i) = Zmod.unsigned (N.v48857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48857 s i)) at 1.
  unfold R.v48857, N.v48857.
  unfold R.v16484, N.v16484.
  rewrite ?node_48856.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48858 (s : N.State) (i : N.Inputs) :
  R.v48858 (state s) (inputs i) = Zmod.unsigned (N.v48858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48858 s i)) at 1.
  unfold R.v48858, N.v48858.
  rewrite ?node_48851.
  rewrite ?node_48852.
  rewrite ?node_48853.
  rewrite ?node_48857.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48859 (s : N.State) (i : N.Inputs) :
  R.v48859 (state s) (inputs i) = Zmod.unsigned (N.v48859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48859 s i)) at 1.
  unfold R.v48859, N.v48859.
  unfold R.v6, N.v6.
  rewrite ?node_48858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48860 (s : N.State) (i : N.Inputs) :
  R.v48860 (state s) (inputs i) = Zmod.unsigned (N.v48860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48860 s i)) at 1.
  unfold R.v48860, N.v48860.
  rewrite ?node_5747.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48861 (s : N.State) (i : N.Inputs) :
  R.v48861 (state s) (inputs i) = Zmod.unsigned (N.v48861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48861 s i)) at 1.
  unfold R.v48861, N.v48861.
  unfold R.v6, N.v6.
  rewrite ?node_5805.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48862 (s : N.State) (i : N.Inputs) :
  R.v48862 (state s) (inputs i) = Zmod.unsigned (N.v48862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48862 s i)) at 1.
  unfold R.v48862, N.v48862.
  unfold R.v6, N.v6.
  rewrite ?node_5809.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48863 (s : N.State) (i : N.Inputs) :
  R.v48863 (state s) (inputs i) = Zmod.unsigned (N.v48863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48863 s i)) at 1.
  unfold R.v48863, N.v48863.
  rewrite ?node_48860.
  rewrite ?node_48861.
  rewrite ?node_48862.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48864 (s : N.State) (i : N.Inputs) :
  R.v48864 (state s) (inputs i) = Zmod.unsigned (N.v48864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48864 s i)) at 1.
  unfold R.v48864, N.v48864.
  rewrite ?node_48859.
  rewrite ?node_48863.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48865 (s : N.State) (i : N.Inputs) :
  R.v48865 (state s) (inputs i) = Zmod.unsigned (N.v48865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48865 s i)) at 1.
  unfold R.v48865, N.v48865.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48866 (s : N.State) (i : N.Inputs) :
  R.v48866 (state s) (inputs i) = Zmod.unsigned (N.v48866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48866 s i)) at 1.
  unfold R.v48866, N.v48866.
  rewrite ?node_5740.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48867 (s : N.State) (i : N.Inputs) :
  R.v48867 (state s) (inputs i) = Zmod.unsigned (N.v48867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48867 s i)) at 1.
  unfold R.v48867, N.v48867.
  unfold R.v6, N.v6.
  rewrite ?node_5736.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48868 (s : N.State) (i : N.Inputs) :
  R.v48868 (state s) (inputs i) = Zmod.unsigned (N.v48868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48868 s i)) at 1.
  unfold R.v48868, N.v48868.
  unfold R.v6, N.v6.
  rewrite ?node_5731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48869 (s : N.State) (i : N.Inputs) :
  R.v48869 (state s) (inputs i) = Zmod.unsigned (N.v48869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48869 s i)) at 1.
  unfold R.v48869, N.v48869.
  rewrite ?node_48867.
  rewrite ?node_48868.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48870 (s : N.State) (i : N.Inputs) :
  R.v48870 (state s) (inputs i) = Zmod.unsigned (N.v48870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48870 s i)) at 1.
  unfold R.v48870, N.v48870.
  unfold R.v16484, N.v16484.
  rewrite ?node_48869.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48871 (s : N.State) (i : N.Inputs) :
  R.v48871 (state s) (inputs i) = Zmod.unsigned (N.v48871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48871 s i)) at 1.
  unfold R.v48871, N.v48871.
  rewrite ?node_48866.
  rewrite ?node_48870.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48872 (s : N.State) (i : N.Inputs) :
  R.v48872 (state s) (inputs i) = Zmod.unsigned (N.v48872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48872 s i)) at 1.
  unfold R.v48872, N.v48872.
  unfold R.v6, N.v6.
  rewrite ?node_48871.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48873 (s : N.State) (i : N.Inputs) :
  R.v48873 (state s) (inputs i) = Zmod.unsigned (N.v48873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48873 s i)) at 1.
  unfold R.v48873, N.v48873.
  rewrite ?node_5741.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48874 (s : N.State) (i : N.Inputs) :
  R.v48874 (state s) (inputs i) = Zmod.unsigned (N.v48874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48874 s i)) at 1.
  unfold R.v48874, N.v48874.
  unfold R.v6, N.v6.
  rewrite ?node_5805.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48875 (s : N.State) (i : N.Inputs) :
  R.v48875 (state s) (inputs i) = Zmod.unsigned (N.v48875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48875 s i)) at 1.
  unfold R.v48875, N.v48875.
  rewrite ?node_48873.
  rewrite ?node_48874.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48876 (s : N.State) (i : N.Inputs) :
  R.v48876 (state s) (inputs i) = Zmod.unsigned (N.v48876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48876 s i)) at 1.
  unfold R.v48876, N.v48876.
  rewrite ?node_48872.
  rewrite ?node_48875.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48877 (s : N.State) (i : N.Inputs) :
  R.v48877 (state s) (inputs i) = Zmod.unsigned (N.v48877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48877 s i)) at 1.
  unfold R.v48877, N.v48877.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48878 (s : N.State) (i : N.Inputs) :
  R.v48878 (state s) (inputs i) = Zmod.unsigned (N.v48878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48878 s i)) at 1.
  unfold R.v48878, N.v48878.
  rewrite ?node_5746.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48879 (s : N.State) (i : N.Inputs) :
  R.v48879 (state s) (inputs i) = Zmod.unsigned (N.v48879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48879 s i)) at 1.
  unfold R.v48879, N.v48879.
  unfold R.v6, N.v6.
  rewrite ?node_5742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48880 (s : N.State) (i : N.Inputs) :
  R.v48880 (state s) (inputs i) = Zmod.unsigned (N.v48880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48880 s i)) at 1.
  unfold R.v48880, N.v48880.
  unfold R.v6, N.v6.
  rewrite ?node_5741.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48881 (s : N.State) (i : N.Inputs) :
  R.v48881 (state s) (inputs i) = Zmod.unsigned (N.v48881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48881 s i)) at 1.
  unfold R.v48881, N.v48881.
  rewrite ?node_48879.
  rewrite ?node_48880.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48882 (s : N.State) (i : N.Inputs) :
  R.v48882 (state s) (inputs i) = Zmod.unsigned (N.v48882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48882 s i)) at 1.
  unfold R.v48882, N.v48882.
  unfold R.v16484, N.v16484.
  rewrite ?node_48881.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48883 (s : N.State) (i : N.Inputs) :
  R.v48883 (state s) (inputs i) = Zmod.unsigned (N.v48883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48883 s i)) at 1.
  unfold R.v48883, N.v48883.
  rewrite ?node_48878.
  rewrite ?node_48882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48884 (s : N.State) (i : N.Inputs) :
  R.v48884 (state s) (inputs i) = Zmod.unsigned (N.v48884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48884 s i)) at 1.
  unfold R.v48884, N.v48884.
  unfold R.v6, N.v6.
  rewrite ?node_48883.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48885 (s : N.State) (i : N.Inputs) :
  R.v48885 (state s) (inputs i) = Zmod.unsigned (N.v48885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48885 s i)) at 1.
  unfold R.v48885, N.v48885.
  rewrite ?node_5747.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48886 (s : N.State) (i : N.Inputs) :
  R.v48886 (state s) (inputs i) = Zmod.unsigned (N.v48886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48886 s i)) at 1.
  unfold R.v48886, N.v48886.
  unfold R.v6, N.v6.
  rewrite ?node_5809.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48887 (s : N.State) (i : N.Inputs) :
  R.v48887 (state s) (inputs i) = Zmod.unsigned (N.v48887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48887 s i)) at 1.
  unfold R.v48887, N.v48887.
  rewrite ?node_48885.
  rewrite ?node_48886.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48888 (s : N.State) (i : N.Inputs) :
  R.v48888 (state s) (inputs i) = Zmod.unsigned (N.v48888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48888 s i)) at 1.
  unfold R.v48888, N.v48888.
  rewrite ?node_48884.
  rewrite ?node_48887.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48889 (s : N.State) (i : N.Inputs) :
  R.v48889 (state s) (inputs i) = Zmod.unsigned (N.v48889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48889 s i)) at 1.
  unfold R.v48889, N.v48889.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48890 (s : N.State) (i : N.Inputs) :
  R.v48890 (state s) (inputs i) = Zmod.unsigned (N.v48890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48890 s i)) at 1.
  unfold R.v48890, N.v48890.
  rewrite ?node_5805.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48891 (s : N.State) (i : N.Inputs) :
  R.v48891 (state s) (inputs i) = Zmod.unsigned (N.v48891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48891 s i)) at 1.
  unfold R.v48891, N.v48891.
  rewrite ?node_5801.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48892 (s : N.State) (i : N.Inputs) :
  R.v48892 (state s) (inputs i) = Zmod.unsigned (N.v48892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48892 s i)) at 1.
  unfold R.v48892, N.v48892.
  rewrite ?node_5799.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48893 (s : N.State) (i : N.Inputs) :
  R.v48893 (state s) (inputs i) = Zmod.unsigned (N.v48893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48893 s i)) at 1.
  unfold R.v48893, N.v48893.
  unfold R.v6, N.v6.
  rewrite ?node_5795.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48894 (s : N.State) (i : N.Inputs) :
  R.v48894 (state s) (inputs i) = Zmod.unsigned (N.v48894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48894 s i)) at 1.
  unfold R.v48894, N.v48894.
  unfold R.v6, N.v6.
  rewrite ?node_5784.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48895 (s : N.State) (i : N.Inputs) :
  R.v48895 (state s) (inputs i) = Zmod.unsigned (N.v48895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48895 s i)) at 1.
  unfold R.v48895, N.v48895.
  rewrite ?node_48893.
  rewrite ?node_48894.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48896 (s : N.State) (i : N.Inputs) :
  R.v48896 (state s) (inputs i) = Zmod.unsigned (N.v48896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48896 s i)) at 1.
  unfold R.v48896, N.v48896.
  unfold R.v16484, N.v16484.
  rewrite ?node_48895.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48897 (s : N.State) (i : N.Inputs) :
  R.v48897 (state s) (inputs i) = Zmod.unsigned (N.v48897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48897 s i)) at 1.
  unfold R.v48897, N.v48897.
  rewrite ?node_48890.
  rewrite ?node_48891.
  rewrite ?node_48892.
  rewrite ?node_48896.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48898 (s : N.State) (i : N.Inputs) :
  R.v48898 (state s) (inputs i) = Zmod.unsigned (N.v48898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48898 s i)) at 1.
  unfold R.v48898, N.v48898.
  unfold R.v6, N.v6.
  rewrite ?node_48897.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48899 (s : N.State) (i : N.Inputs) :
  R.v48899 (state s) (inputs i) = Zmod.unsigned (N.v48899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48899 s i)) at 1.
  unfold R.v48899, N.v48899.
  rewrite ?node_5806.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48900 (s : N.State) (i : N.Inputs) :
  R.v48900 (state s) (inputs i) = Zmod.unsigned (N.v48900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48900 s i)) at 1.
  unfold R.v48900, N.v48900.
  unfold R.v6, N.v6.
  rewrite ?node_5866.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48901 (s : N.State) (i : N.Inputs) :
  R.v48901 (state s) (inputs i) = Zmod.unsigned (N.v48901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48901 s i)) at 1.
  unfold R.v48901, N.v48901.
  unfold R.v6, N.v6.
  rewrite ?node_5870.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48902 (s : N.State) (i : N.Inputs) :
  R.v48902 (state s) (inputs i) = Zmod.unsigned (N.v48902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48902 s i)) at 1.
  unfold R.v48902, N.v48902.
  rewrite ?node_48899.
  rewrite ?node_48900.
  rewrite ?node_48901.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48903 (s : N.State) (i : N.Inputs) :
  R.v48903 (state s) (inputs i) = Zmod.unsigned (N.v48903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48903 s i)) at 1.
  unfold R.v48903, N.v48903.
  rewrite ?node_48898.
  rewrite ?node_48902.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48904 (s : N.State) (i : N.Inputs) :
  R.v48904 (state s) (inputs i) = Zmod.unsigned (N.v48904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48904 s i)) at 1.
  unfold R.v48904, N.v48904.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48905 (s : N.State) (i : N.Inputs) :
  R.v48905 (state s) (inputs i) = Zmod.unsigned (N.v48905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48905 s i)) at 1.
  unfold R.v48905, N.v48905.
  rewrite ?node_5799.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48906 (s : N.State) (i : N.Inputs) :
  R.v48906 (state s) (inputs i) = Zmod.unsigned (N.v48906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48906 s i)) at 1.
  unfold R.v48906, N.v48906.
  unfold R.v6, N.v6.
  rewrite ?node_5795.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48907 (s : N.State) (i : N.Inputs) :
  R.v48907 (state s) (inputs i) = Zmod.unsigned (N.v48907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48907 s i)) at 1.
  unfold R.v48907, N.v48907.
  unfold R.v6, N.v6.
  rewrite ?node_5784.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48908 (s : N.State) (i : N.Inputs) :
  R.v48908 (state s) (inputs i) = Zmod.unsigned (N.v48908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48908 s i)) at 1.
  unfold R.v48908, N.v48908.
  rewrite ?node_48906.
  rewrite ?node_48907.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48909 (s : N.State) (i : N.Inputs) :
  R.v48909 (state s) (inputs i) = Zmod.unsigned (N.v48909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48909 s i)) at 1.
  unfold R.v48909, N.v48909.
  unfold R.v16484, N.v16484.
  rewrite ?node_48908.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48910 (s : N.State) (i : N.Inputs) :
  R.v48910 (state s) (inputs i) = Zmod.unsigned (N.v48910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48910 s i)) at 1.
  unfold R.v48910, N.v48910.
  rewrite ?node_48905.
  rewrite ?node_48909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48911 (s : N.State) (i : N.Inputs) :
  R.v48911 (state s) (inputs i) = Zmod.unsigned (N.v48911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48911 s i)) at 1.
  unfold R.v48911, N.v48911.
  unfold R.v6, N.v6.
  rewrite ?node_48910.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48912 (s : N.State) (i : N.Inputs) :
  R.v48912 (state s) (inputs i) = Zmod.unsigned (N.v48912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48912 s i)) at 1.
  unfold R.v48912, N.v48912.
  rewrite ?node_5800.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48913 (s : N.State) (i : N.Inputs) :
  R.v48913 (state s) (inputs i) = Zmod.unsigned (N.v48913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48913 s i)) at 1.
  unfold R.v48913, N.v48913.
  unfold R.v6, N.v6.
  rewrite ?node_5866.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48914 (s : N.State) (i : N.Inputs) :
  R.v48914 (state s) (inputs i) = Zmod.unsigned (N.v48914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48914 s i)) at 1.
  unfold R.v48914, N.v48914.
  rewrite ?node_48912.
  rewrite ?node_48913.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48915 (s : N.State) (i : N.Inputs) :
  R.v48915 (state s) (inputs i) = Zmod.unsigned (N.v48915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48915 s i)) at 1.
  unfold R.v48915, N.v48915.
  rewrite ?node_48911.
  rewrite ?node_48914.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48916 (s : N.State) (i : N.Inputs) :
  R.v48916 (state s) (inputs i) = Zmod.unsigned (N.v48916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48916 s i)) at 1.
  unfold R.v48916, N.v48916.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48917 (s : N.State) (i : N.Inputs) :
  R.v48917 (state s) (inputs i) = Zmod.unsigned (N.v48917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48917 s i)) at 1.
  unfold R.v48917, N.v48917.
  rewrite ?node_5805.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48918 (s : N.State) (i : N.Inputs) :
  R.v48918 (state s) (inputs i) = Zmod.unsigned (N.v48918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48918 s i)) at 1.
  unfold R.v48918, N.v48918.
  unfold R.v6, N.v6.
  rewrite ?node_5801.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48919 (s : N.State) (i : N.Inputs) :
  R.v48919 (state s) (inputs i) = Zmod.unsigned (N.v48919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48919 s i)) at 1.
  unfold R.v48919, N.v48919.
  unfold R.v6, N.v6.
  rewrite ?node_5800.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48920 (s : N.State) (i : N.Inputs) :
  R.v48920 (state s) (inputs i) = Zmod.unsigned (N.v48920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48920 s i)) at 1.
  unfold R.v48920, N.v48920.
  rewrite ?node_48918.
  rewrite ?node_48919.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48921 (s : N.State) (i : N.Inputs) :
  R.v48921 (state s) (inputs i) = Zmod.unsigned (N.v48921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48921 s i)) at 1.
  unfold R.v48921, N.v48921.
  unfold R.v16484, N.v16484.
  rewrite ?node_48920.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48922 (s : N.State) (i : N.Inputs) :
  R.v48922 (state s) (inputs i) = Zmod.unsigned (N.v48922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48922 s i)) at 1.
  unfold R.v48922, N.v48922.
  rewrite ?node_48917.
  rewrite ?node_48921.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48923 (s : N.State) (i : N.Inputs) :
  R.v48923 (state s) (inputs i) = Zmod.unsigned (N.v48923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48923 s i)) at 1.
  unfold R.v48923, N.v48923.
  unfold R.v6, N.v6.
  rewrite ?node_48922.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48924 (s : N.State) (i : N.Inputs) :
  R.v48924 (state s) (inputs i) = Zmod.unsigned (N.v48924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48924 s i)) at 1.
  unfold R.v48924, N.v48924.
  rewrite ?node_5806.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48925 (s : N.State) (i : N.Inputs) :
  R.v48925 (state s) (inputs i) = Zmod.unsigned (N.v48925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48925 s i)) at 1.
  unfold R.v48925, N.v48925.
  unfold R.v6, N.v6.
  rewrite ?node_5870.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48926 (s : N.State) (i : N.Inputs) :
  R.v48926 (state s) (inputs i) = Zmod.unsigned (N.v48926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48926 s i)) at 1.
  unfold R.v48926, N.v48926.
  rewrite ?node_48924.
  rewrite ?node_48925.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48927 (s : N.State) (i : N.Inputs) :
  R.v48927 (state s) (inputs i) = Zmod.unsigned (N.v48927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48927 s i)) at 1.
  unfold R.v48927, N.v48927.
  rewrite ?node_48923.
  rewrite ?node_48926.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48928 (s : N.State) (i : N.Inputs) :
  R.v48928 (state s) (inputs i) = Zmod.unsigned (N.v48928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48928 s i)) at 1.
  unfold R.v48928, N.v48928.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48929 (s : N.State) (i : N.Inputs) :
  R.v48929 (state s) (inputs i) = Zmod.unsigned (N.v48929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48929 s i)) at 1.
  unfold R.v48929, N.v48929.
  rewrite ?node_5866.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48930 (s : N.State) (i : N.Inputs) :
  R.v48930 (state s) (inputs i) = Zmod.unsigned (N.v48930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48930 s i)) at 1.
  unfold R.v48930, N.v48930.
  rewrite ?node_5862.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48931 (s : N.State) (i : N.Inputs) :
  R.v48931 (state s) (inputs i) = Zmod.unsigned (N.v48931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48931 s i)) at 1.
  unfold R.v48931, N.v48931.
  rewrite ?node_5858.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48932 (s : N.State) (i : N.Inputs) :
  R.v48932 (state s) (inputs i) = Zmod.unsigned (N.v48932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48932 s i)) at 1.
  unfold R.v48932, N.v48932.
  unfold R.v6, N.v6.
  rewrite ?node_5854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48933 (s : N.State) (i : N.Inputs) :
  R.v48933 (state s) (inputs i) = Zmod.unsigned (N.v48933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48933 s i)) at 1.
  unfold R.v48933, N.v48933.
  unfold R.v6, N.v6.
  rewrite ?node_5843.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48934 (s : N.State) (i : N.Inputs) :
  R.v48934 (state s) (inputs i) = Zmod.unsigned (N.v48934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48934 s i)) at 1.
  unfold R.v48934, N.v48934.
  rewrite ?node_48932.
  rewrite ?node_48933.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48935 (s : N.State) (i : N.Inputs) :
  R.v48935 (state s) (inputs i) = Zmod.unsigned (N.v48935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48935 s i)) at 1.
  unfold R.v48935, N.v48935.
  unfold R.v16484, N.v16484.
  rewrite ?node_48934.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48936 (s : N.State) (i : N.Inputs) :
  R.v48936 (state s) (inputs i) = Zmod.unsigned (N.v48936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48936 s i)) at 1.
  unfold R.v48936, N.v48936.
  rewrite ?node_48929.
  rewrite ?node_48930.
  rewrite ?node_48931.
  rewrite ?node_48935.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48937 (s : N.State) (i : N.Inputs) :
  R.v48937 (state s) (inputs i) = Zmod.unsigned (N.v48937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48937 s i)) at 1.
  unfold R.v48937, N.v48937.
  unfold R.v6, N.v6.
  rewrite ?node_48936.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48938 (s : N.State) (i : N.Inputs) :
  R.v48938 (state s) (inputs i) = Zmod.unsigned (N.v48938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48938 s i)) at 1.
  unfold R.v48938, N.v48938.
  rewrite ?node_5867.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48939 (s : N.State) (i : N.Inputs) :
  R.v48939 (state s) (inputs i) = Zmod.unsigned (N.v48939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48939 s i)) at 1.
  unfold R.v48939, N.v48939.
  unfold R.v6, N.v6.
  rewrite ?node_5928.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48940 (s : N.State) (i : N.Inputs) :
  R.v48940 (state s) (inputs i) = Zmod.unsigned (N.v48940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48940 s i)) at 1.
  unfold R.v48940, N.v48940.
  unfold R.v6, N.v6.
  rewrite ?node_5932.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48941 (s : N.State) (i : N.Inputs) :
  R.v48941 (state s) (inputs i) = Zmod.unsigned (N.v48941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48941 s i)) at 1.
  unfold R.v48941, N.v48941.
  rewrite ?node_48938.
  rewrite ?node_48939.
  rewrite ?node_48940.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48942 (s : N.State) (i : N.Inputs) :
  R.v48942 (state s) (inputs i) = Zmod.unsigned (N.v48942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48942 s i)) at 1.
  unfold R.v48942, N.v48942.
  rewrite ?node_48937.
  rewrite ?node_48941.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48943 (s : N.State) (i : N.Inputs) :
  R.v48943 (state s) (inputs i) = Zmod.unsigned (N.v48943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48943 s i)) at 1.
  unfold R.v48943, N.v48943.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48944 (s : N.State) (i : N.Inputs) :
  R.v48944 (state s) (inputs i) = Zmod.unsigned (N.v48944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48944 s i)) at 1.
  unfold R.v48944, N.v48944.
  rewrite ?node_5858.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48945 (s : N.State) (i : N.Inputs) :
  R.v48945 (state s) (inputs i) = Zmod.unsigned (N.v48945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48945 s i)) at 1.
  unfold R.v48945, N.v48945.
  unfold R.v6, N.v6.
  rewrite ?node_5854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48946 (s : N.State) (i : N.Inputs) :
  R.v48946 (state s) (inputs i) = Zmod.unsigned (N.v48946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48946 s i)) at 1.
  unfold R.v48946, N.v48946.
  unfold R.v6, N.v6.
  rewrite ?node_5843.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48947 (s : N.State) (i : N.Inputs) :
  R.v48947 (state s) (inputs i) = Zmod.unsigned (N.v48947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48947 s i)) at 1.
  unfold R.v48947, N.v48947.
  rewrite ?node_48945.
  rewrite ?node_48946.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48948 (s : N.State) (i : N.Inputs) :
  R.v48948 (state s) (inputs i) = Zmod.unsigned (N.v48948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48948 s i)) at 1.
  unfold R.v48948, N.v48948.
  unfold R.v16484, N.v16484.
  rewrite ?node_48947.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48949 (s : N.State) (i : N.Inputs) :
  R.v48949 (state s) (inputs i) = Zmod.unsigned (N.v48949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48949 s i)) at 1.
  unfold R.v48949, N.v48949.
  rewrite ?node_48944.
  rewrite ?node_48948.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48950 (s : N.State) (i : N.Inputs) :
  R.v48950 (state s) (inputs i) = Zmod.unsigned (N.v48950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48950 s i)) at 1.
  unfold R.v48950, N.v48950.
  unfold R.v6, N.v6.
  rewrite ?node_48949.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48951 (s : N.State) (i : N.Inputs) :
  R.v48951 (state s) (inputs i) = Zmod.unsigned (N.v48951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48951 s i)) at 1.
  unfold R.v48951, N.v48951.
  rewrite ?node_5859.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48952 (s : N.State) (i : N.Inputs) :
  R.v48952 (state s) (inputs i) = Zmod.unsigned (N.v48952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48952 s i)) at 1.
  unfold R.v48952, N.v48952.
  unfold R.v6, N.v6.
  rewrite ?node_5928.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48953 (s : N.State) (i : N.Inputs) :
  R.v48953 (state s) (inputs i) = Zmod.unsigned (N.v48953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48953 s i)) at 1.
  unfold R.v48953, N.v48953.
  rewrite ?node_48951.
  rewrite ?node_48952.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48954 (s : N.State) (i : N.Inputs) :
  R.v48954 (state s) (inputs i) = Zmod.unsigned (N.v48954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48954 s i)) at 1.
  unfold R.v48954, N.v48954.
  rewrite ?node_48950.
  rewrite ?node_48953.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48955 (s : N.State) (i : N.Inputs) :
  R.v48955 (state s) (inputs i) = Zmod.unsigned (N.v48955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48955 s i)) at 1.
  unfold R.v48955, N.v48955.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48956 (s : N.State) (i : N.Inputs) :
  R.v48956 (state s) (inputs i) = Zmod.unsigned (N.v48956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48956 s i)) at 1.
  unfold R.v48956, N.v48956.
  rewrite ?node_5866.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48957 (s : N.State) (i : N.Inputs) :
  R.v48957 (state s) (inputs i) = Zmod.unsigned (N.v48957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48957 s i)) at 1.
  unfold R.v48957, N.v48957.
  unfold R.v6, N.v6.
  rewrite ?node_5862.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48958 (s : N.State) (i : N.Inputs) :
  R.v48958 (state s) (inputs i) = Zmod.unsigned (N.v48958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48958 s i)) at 1.
  unfold R.v48958, N.v48958.
  unfold R.v6, N.v6.
  rewrite ?node_5859.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48959 (s : N.State) (i : N.Inputs) :
  R.v48959 (state s) (inputs i) = Zmod.unsigned (N.v48959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48959 s i)) at 1.
  unfold R.v48959, N.v48959.
  rewrite ?node_48957.
  rewrite ?node_48958.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48960 (s : N.State) (i : N.Inputs) :
  R.v48960 (state s) (inputs i) = Zmod.unsigned (N.v48960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48960 s i)) at 1.
  unfold R.v48960, N.v48960.
  unfold R.v16484, N.v16484.
  rewrite ?node_48959.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48961 (s : N.State) (i : N.Inputs) :
  R.v48961 (state s) (inputs i) = Zmod.unsigned (N.v48961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48961 s i)) at 1.
  unfold R.v48961, N.v48961.
  rewrite ?node_48956.
  rewrite ?node_48960.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48962 (s : N.State) (i : N.Inputs) :
  R.v48962 (state s) (inputs i) = Zmod.unsigned (N.v48962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48962 s i)) at 1.
  unfold R.v48962, N.v48962.
  unfold R.v6, N.v6.
  rewrite ?node_48961.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48963 (s : N.State) (i : N.Inputs) :
  R.v48963 (state s) (inputs i) = Zmod.unsigned (N.v48963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48963 s i)) at 1.
  unfold R.v48963, N.v48963.
  rewrite ?node_5867.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48964 (s : N.State) (i : N.Inputs) :
  R.v48964 (state s) (inputs i) = Zmod.unsigned (N.v48964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48964 s i)) at 1.
  unfold R.v48964, N.v48964.
  unfold R.v6, N.v6.
  rewrite ?node_5932.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48965 (s : N.State) (i : N.Inputs) :
  R.v48965 (state s) (inputs i) = Zmod.unsigned (N.v48965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48965 s i)) at 1.
  unfold R.v48965, N.v48965.
  rewrite ?node_48963.
  rewrite ?node_48964.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48966 (s : N.State) (i : N.Inputs) :
  R.v48966 (state s) (inputs i) = Zmod.unsigned (N.v48966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48966 s i)) at 1.
  unfold R.v48966, N.v48966.
  rewrite ?node_48962.
  rewrite ?node_48965.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48967 (s : N.State) (i : N.Inputs) :
  R.v48967 (state s) (inputs i) = Zmod.unsigned (N.v48967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48967 s i)) at 1.
  unfold R.v48967, N.v48967.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48968 (s : N.State) (i : N.Inputs) :
  R.v48968 (state s) (inputs i) = Zmod.unsigned (N.v48968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48968 s i)) at 1.
  unfold R.v48968, N.v48968.
  rewrite ?node_5928.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48969 (s : N.State) (i : N.Inputs) :
  R.v48969 (state s) (inputs i) = Zmod.unsigned (N.v48969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48969 s i)) at 1.
  unfold R.v48969, N.v48969.
  rewrite ?node_5924.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48970 (s : N.State) (i : N.Inputs) :
  R.v48970 (state s) (inputs i) = Zmod.unsigned (N.v48970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48970 s i)) at 1.
  unfold R.v48970, N.v48970.
  rewrite ?node_5920.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48971 (s : N.State) (i : N.Inputs) :
  R.v48971 (state s) (inputs i) = Zmod.unsigned (N.v48971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48971 s i)) at 1.
  unfold R.v48971, N.v48971.
  unfold R.v6, N.v6.
  rewrite ?node_5916.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48972 (s : N.State) (i : N.Inputs) :
  R.v48972 (state s) (inputs i) = Zmod.unsigned (N.v48972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48972 s i)) at 1.
  unfold R.v48972, N.v48972.
  unfold R.v6, N.v6.
  rewrite ?node_5905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48973 (s : N.State) (i : N.Inputs) :
  R.v48973 (state s) (inputs i) = Zmod.unsigned (N.v48973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48973 s i)) at 1.
  unfold R.v48973, N.v48973.
  rewrite ?node_48971.
  rewrite ?node_48972.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48974 (s : N.State) (i : N.Inputs) :
  R.v48974 (state s) (inputs i) = Zmod.unsigned (N.v48974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48974 s i)) at 1.
  unfold R.v48974, N.v48974.
  unfold R.v16484, N.v16484.
  rewrite ?node_48973.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48975 (s : N.State) (i : N.Inputs) :
  R.v48975 (state s) (inputs i) = Zmod.unsigned (N.v48975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48975 s i)) at 1.
  unfold R.v48975, N.v48975.
  rewrite ?node_48968.
  rewrite ?node_48969.
  rewrite ?node_48970.
  rewrite ?node_48974.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48976 (s : N.State) (i : N.Inputs) :
  R.v48976 (state s) (inputs i) = Zmod.unsigned (N.v48976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48976 s i)) at 1.
  unfold R.v48976, N.v48976.
  unfold R.v6, N.v6.
  rewrite ?node_48975.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48977 (s : N.State) (i : N.Inputs) :
  R.v48977 (state s) (inputs i) = Zmod.unsigned (N.v48977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48977 s i)) at 1.
  unfold R.v48977, N.v48977.
  rewrite ?node_5929.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48978 (s : N.State) (i : N.Inputs) :
  R.v48978 (state s) (inputs i) = Zmod.unsigned (N.v48978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48978 s i)) at 1.
  unfold R.v48978, N.v48978.
  unfold R.v6, N.v6.
  rewrite ?node_5992.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48979 (s : N.State) (i : N.Inputs) :
  R.v48979 (state s) (inputs i) = Zmod.unsigned (N.v48979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48979 s i)) at 1.
  unfold R.v48979, N.v48979.
  unfold R.v6, N.v6.
  rewrite ?node_5996.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48980 (s : N.State) (i : N.Inputs) :
  R.v48980 (state s) (inputs i) = Zmod.unsigned (N.v48980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48980 s i)) at 1.
  unfold R.v48980, N.v48980.
  rewrite ?node_48977.
  rewrite ?node_48978.
  rewrite ?node_48979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48981 (s : N.State) (i : N.Inputs) :
  R.v48981 (state s) (inputs i) = Zmod.unsigned (N.v48981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48981 s i)) at 1.
  unfold R.v48981, N.v48981.
  rewrite ?node_48976.
  rewrite ?node_48980.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48982 (s : N.State) (i : N.Inputs) :
  R.v48982 (state s) (inputs i) = Zmod.unsigned (N.v48982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48982 s i)) at 1.
  unfold R.v48982, N.v48982.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48983 (s : N.State) (i : N.Inputs) :
  R.v48983 (state s) (inputs i) = Zmod.unsigned (N.v48983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48983 s i)) at 1.
  unfold R.v48983, N.v48983.
  rewrite ?node_5920.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48984 (s : N.State) (i : N.Inputs) :
  R.v48984 (state s) (inputs i) = Zmod.unsigned (N.v48984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48984 s i)) at 1.
  unfold R.v48984, N.v48984.
  unfold R.v6, N.v6.
  rewrite ?node_5916.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48985 (s : N.State) (i : N.Inputs) :
  R.v48985 (state s) (inputs i) = Zmod.unsigned (N.v48985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48985 s i)) at 1.
  unfold R.v48985, N.v48985.
  unfold R.v6, N.v6.
  rewrite ?node_5905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48986 (s : N.State) (i : N.Inputs) :
  R.v48986 (state s) (inputs i) = Zmod.unsigned (N.v48986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48986 s i)) at 1.
  unfold R.v48986, N.v48986.
  rewrite ?node_48984.
  rewrite ?node_48985.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48987 (s : N.State) (i : N.Inputs) :
  R.v48987 (state s) (inputs i) = Zmod.unsigned (N.v48987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48987 s i)) at 1.
  unfold R.v48987, N.v48987.
  unfold R.v16484, N.v16484.
  rewrite ?node_48986.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48988 (s : N.State) (i : N.Inputs) :
  R.v48988 (state s) (inputs i) = Zmod.unsigned (N.v48988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48988 s i)) at 1.
  unfold R.v48988, N.v48988.
  rewrite ?node_48983.
  rewrite ?node_48987.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48989 (s : N.State) (i : N.Inputs) :
  R.v48989 (state s) (inputs i) = Zmod.unsigned (N.v48989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48989 s i)) at 1.
  unfold R.v48989, N.v48989.
  unfold R.v6, N.v6.
  rewrite ?node_48988.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48990 (s : N.State) (i : N.Inputs) :
  R.v48990 (state s) (inputs i) = Zmod.unsigned (N.v48990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48990 s i)) at 1.
  unfold R.v48990, N.v48990.
  rewrite ?node_5921.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48991 (s : N.State) (i : N.Inputs) :
  R.v48991 (state s) (inputs i) = Zmod.unsigned (N.v48991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48991 s i)) at 1.
  unfold R.v48991, N.v48991.
  unfold R.v6, N.v6.
  rewrite ?node_5992.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48992 (s : N.State) (i : N.Inputs) :
  R.v48992 (state s) (inputs i) = Zmod.unsigned (N.v48992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48992 s i)) at 1.
  unfold R.v48992, N.v48992.
  rewrite ?node_48990.
  rewrite ?node_48991.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48993 (s : N.State) (i : N.Inputs) :
  R.v48993 (state s) (inputs i) = Zmod.unsigned (N.v48993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48993 s i)) at 1.
  unfold R.v48993, N.v48993.
  rewrite ?node_48989.
  rewrite ?node_48992.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48994 (s : N.State) (i : N.Inputs) :
  R.v48994 (state s) (inputs i) = Zmod.unsigned (N.v48994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48994 s i)) at 1.
  unfold R.v48994, N.v48994.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48995 (s : N.State) (i : N.Inputs) :
  R.v48995 (state s) (inputs i) = Zmod.unsigned (N.v48995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48995 s i)) at 1.
  unfold R.v48995, N.v48995.
  rewrite ?node_5928.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48996 (s : N.State) (i : N.Inputs) :
  R.v48996 (state s) (inputs i) = Zmod.unsigned (N.v48996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48996 s i)) at 1.
  unfold R.v48996, N.v48996.
  unfold R.v6, N.v6.
  rewrite ?node_5924.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48997 (s : N.State) (i : N.Inputs) :
  R.v48997 (state s) (inputs i) = Zmod.unsigned (N.v48997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48997 s i)) at 1.
  unfold R.v48997, N.v48997.
  unfold R.v6, N.v6.
  rewrite ?node_5921.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48998 (s : N.State) (i : N.Inputs) :
  R.v48998 (state s) (inputs i) = Zmod.unsigned (N.v48998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48998 s i)) at 1.
  unfold R.v48998, N.v48998.
  rewrite ?node_48996.
  rewrite ?node_48997.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_48999 (s : N.State) (i : N.Inputs) :
  R.v48999 (state s) (inputs i) = Zmod.unsigned (N.v48999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v48999 s i)) at 1.
  unfold R.v48999, N.v48999.
  unfold R.v16484, N.v16484.
  rewrite ?node_48998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
