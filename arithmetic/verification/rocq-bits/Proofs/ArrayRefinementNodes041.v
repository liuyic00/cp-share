(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes040.
Lemma node_41000 (s : N.State) (i : N.Inputs) :
  R.v41000 (state s) (inputs i) = Zmod.unsigned (N.v41000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41000 s i)) at 1.
  unfold R.v41000, N.v41000.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41001 (s : N.State) (i : N.Inputs) :
  R.v41001 (state s) (inputs i) = Zmod.unsigned (N.v41001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41001 s i)) at 1.
  unfold R.v41001, N.v41001.
  rewrite ?node_8471.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41002 (s : N.State) (i : N.Inputs) :
  R.v41002 (state s) (inputs i) = Zmod.unsigned (N.v41002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41002 s i)) at 1.
  unfold R.v41002, N.v41002.
  unfold R.v6, N.v6.
  rewrite ?node_8468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41003 (s : N.State) (i : N.Inputs) :
  R.v41003 (state s) (inputs i) = Zmod.unsigned (N.v41003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41003 s i)) at 1.
  unfold R.v41003, N.v41003.
  unfold R.v6, N.v6.
  rewrite ?node_8461.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41004 (s : N.State) (i : N.Inputs) :
  R.v41004 (state s) (inputs i) = Zmod.unsigned (N.v41004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41004 s i)) at 1.
  unfold R.v41004, N.v41004.
  rewrite ?node_41002.
  rewrite ?node_41003.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41005 (s : N.State) (i : N.Inputs) :
  R.v41005 (state s) (inputs i) = Zmod.unsigned (N.v41005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41005 s i)) at 1.
  unfold R.v41005, N.v41005.
  unfold R.v16484, N.v16484.
  rewrite ?node_41004.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41006 (s : N.State) (i : N.Inputs) :
  R.v41006 (state s) (inputs i) = Zmod.unsigned (N.v41006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41006 s i)) at 1.
  unfold R.v41006, N.v41006.
  rewrite ?node_41001.
  rewrite ?node_41005.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41007 (s : N.State) (i : N.Inputs) :
  R.v41007 (state s) (inputs i) = Zmod.unsigned (N.v41007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41007 s i)) at 1.
  unfold R.v41007, N.v41007.
  unfold R.v6, N.v6.
  rewrite ?node_41006.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41008 (s : N.State) (i : N.Inputs) :
  R.v41008 (state s) (inputs i) = Zmod.unsigned (N.v41008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41008 s i)) at 1.
  unfold R.v41008, N.v41008.
  rewrite ?node_8472.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41009 (s : N.State) (i : N.Inputs) :
  R.v41009 (state s) (inputs i) = Zmod.unsigned (N.v41009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41009 s i)) at 1.
  unfold R.v41009, N.v41009.
  unfold R.v6, N.v6.
  rewrite ?node_8609.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41010 (s : N.State) (i : N.Inputs) :
  R.v41010 (state s) (inputs i) = Zmod.unsigned (N.v41010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41010 s i)) at 1.
  unfold R.v41010, N.v41010.
  rewrite ?node_41008.
  rewrite ?node_41009.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41011 (s : N.State) (i : N.Inputs) :
  R.v41011 (state s) (inputs i) = Zmod.unsigned (N.v41011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41011 s i)) at 1.
  unfold R.v41011, N.v41011.
  rewrite ?node_41007.
  rewrite ?node_41010.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41012 (s : N.State) (i : N.Inputs) :
  R.v41012 (state s) (inputs i) = Zmod.unsigned (N.v41012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41012 s i)) at 1.
  unfold R.v41012, N.v41012.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41013 (s : N.State) (i : N.Inputs) :
  R.v41013 (state s) (inputs i) = Zmod.unsigned (N.v41013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41013 s i)) at 1.
  unfold R.v41013, N.v41013.
  rewrite ?node_8479.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41014 (s : N.State) (i : N.Inputs) :
  R.v41014 (state s) (inputs i) = Zmod.unsigned (N.v41014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41014 s i)) at 1.
  unfold R.v41014, N.v41014.
  unfold R.v6, N.v6.
  rewrite ?node_8475.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41015 (s : N.State) (i : N.Inputs) :
  R.v41015 (state s) (inputs i) = Zmod.unsigned (N.v41015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41015 s i)) at 1.
  unfold R.v41015, N.v41015.
  unfold R.v6, N.v6.
  rewrite ?node_8472.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41016 (s : N.State) (i : N.Inputs) :
  R.v41016 (state s) (inputs i) = Zmod.unsigned (N.v41016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41016 s i)) at 1.
  unfold R.v41016, N.v41016.
  rewrite ?node_41014.
  rewrite ?node_41015.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41017 (s : N.State) (i : N.Inputs) :
  R.v41017 (state s) (inputs i) = Zmod.unsigned (N.v41017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41017 s i)) at 1.
  unfold R.v41017, N.v41017.
  unfold R.v16484, N.v16484.
  rewrite ?node_41016.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41018 (s : N.State) (i : N.Inputs) :
  R.v41018 (state s) (inputs i) = Zmod.unsigned (N.v41018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41018 s i)) at 1.
  unfold R.v41018, N.v41018.
  rewrite ?node_41013.
  rewrite ?node_41017.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41019 (s : N.State) (i : N.Inputs) :
  R.v41019 (state s) (inputs i) = Zmod.unsigned (N.v41019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41019 s i)) at 1.
  unfold R.v41019, N.v41019.
  unfold R.v6, N.v6.
  rewrite ?node_41018.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41020 (s : N.State) (i : N.Inputs) :
  R.v41020 (state s) (inputs i) = Zmod.unsigned (N.v41020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41020 s i)) at 1.
  unfold R.v41020, N.v41020.
  rewrite ?node_8480.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41021 (s : N.State) (i : N.Inputs) :
  R.v41021 (state s) (inputs i) = Zmod.unsigned (N.v41021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41021 s i)) at 1.
  unfold R.v41021, N.v41021.
  unfold R.v6, N.v6.
  rewrite ?node_8649.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41022 (s : N.State) (i : N.Inputs) :
  R.v41022 (state s) (inputs i) = Zmod.unsigned (N.v41022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41022 s i)) at 1.
  unfold R.v41022, N.v41022.
  rewrite ?node_41020.
  rewrite ?node_41021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41023 (s : N.State) (i : N.Inputs) :
  R.v41023 (state s) (inputs i) = Zmod.unsigned (N.v41023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41023 s i)) at 1.
  unfold R.v41023, N.v41023.
  rewrite ?node_41019.
  rewrite ?node_41022.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41024 (s : N.State) (i : N.Inputs) :
  R.v41024 (state s) (inputs i) = Zmod.unsigned (N.v41024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41024 s i)) at 1.
  unfold R.v41024, N.v41024.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41025 (s : N.State) (i : N.Inputs) :
  R.v41025 (state s) (inputs i) = Zmod.unsigned (N.v41025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41025 s i)) at 1.
  unfold R.v41025, N.v41025.
  rewrite ?node_8499.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41026 (s : N.State) (i : N.Inputs) :
  R.v41026 (state s) (inputs i) = Zmod.unsigned (N.v41026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41026 s i)) at 1.
  unfold R.v41026, N.v41026.
  rewrite ?node_8495.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41027 (s : N.State) (i : N.Inputs) :
  R.v41027 (state s) (inputs i) = Zmod.unsigned (N.v41027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41027 s i)) at 1.
  unfold R.v41027, N.v41027.
  rewrite ?node_8491.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41028 (s : N.State) (i : N.Inputs) :
  R.v41028 (state s) (inputs i) = Zmod.unsigned (N.v41028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41028 s i)) at 1.
  unfold R.v41028, N.v41028.
  unfold R.v6, N.v6.
  rewrite ?node_8487.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41029 (s : N.State) (i : N.Inputs) :
  R.v41029 (state s) (inputs i) = Zmod.unsigned (N.v41029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41029 s i)) at 1.
  unfold R.v41029, N.v41029.
  unfold R.v6, N.v6.
  rewrite ?node_8484.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41030 (s : N.State) (i : N.Inputs) :
  R.v41030 (state s) (inputs i) = Zmod.unsigned (N.v41030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41030 s i)) at 1.
  unfold R.v41030, N.v41030.
  rewrite ?node_41028.
  rewrite ?node_41029.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41031 (s : N.State) (i : N.Inputs) :
  R.v41031 (state s) (inputs i) = Zmod.unsigned (N.v41031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41031 s i)) at 1.
  unfold R.v41031, N.v41031.
  unfold R.v16484, N.v16484.
  rewrite ?node_41030.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41032 (s : N.State) (i : N.Inputs) :
  R.v41032 (state s) (inputs i) = Zmod.unsigned (N.v41032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41032 s i)) at 1.
  unfold R.v41032, N.v41032.
  rewrite ?node_41025.
  rewrite ?node_41026.
  rewrite ?node_41027.
  rewrite ?node_41031.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41033 (s : N.State) (i : N.Inputs) :
  R.v41033 (state s) (inputs i) = Zmod.unsigned (N.v41033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41033 s i)) at 1.
  unfold R.v41033, N.v41033.
  unfold R.v6, N.v6.
  rewrite ?node_41032.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41034 (s : N.State) (i : N.Inputs) :
  R.v41034 (state s) (inputs i) = Zmod.unsigned (N.v41034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41034 s i)) at 1.
  unfold R.v41034, N.v41034.
  rewrite ?node_8500.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41035 (s : N.State) (i : N.Inputs) :
  R.v41035 (state s) (inputs i) = Zmod.unsigned (N.v41035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41035 s i)) at 1.
  unfold R.v41035, N.v41035.
  unfold R.v6, N.v6.
  rewrite ?node_8629.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41036 (s : N.State) (i : N.Inputs) :
  R.v41036 (state s) (inputs i) = Zmod.unsigned (N.v41036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41036 s i)) at 1.
  unfold R.v41036, N.v41036.
  unfold R.v6, N.v6.
  rewrite ?node_8653.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41037 (s : N.State) (i : N.Inputs) :
  R.v41037 (state s) (inputs i) = Zmod.unsigned (N.v41037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41037 s i)) at 1.
  unfold R.v41037, N.v41037.
  rewrite ?node_41034.
  rewrite ?node_41035.
  rewrite ?node_41036.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41038 (s : N.State) (i : N.Inputs) :
  R.v41038 (state s) (inputs i) = Zmod.unsigned (N.v41038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41038 s i)) at 1.
  unfold R.v41038, N.v41038.
  rewrite ?node_41033.
  rewrite ?node_41037.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41039 (s : N.State) (i : N.Inputs) :
  R.v41039 (state s) (inputs i) = Zmod.unsigned (N.v41039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41039 s i)) at 1.
  unfold R.v41039, N.v41039.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41040 (s : N.State) (i : N.Inputs) :
  R.v41040 (state s) (inputs i) = Zmod.unsigned (N.v41040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41040 s i)) at 1.
  unfold R.v41040, N.v41040.
  rewrite ?node_8491.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41041 (s : N.State) (i : N.Inputs) :
  R.v41041 (state s) (inputs i) = Zmod.unsigned (N.v41041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41041 s i)) at 1.
  unfold R.v41041, N.v41041.
  unfold R.v6, N.v6.
  rewrite ?node_8487.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41042 (s : N.State) (i : N.Inputs) :
  R.v41042 (state s) (inputs i) = Zmod.unsigned (N.v41042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41042 s i)) at 1.
  unfold R.v41042, N.v41042.
  unfold R.v6, N.v6.
  rewrite ?node_8484.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41043 (s : N.State) (i : N.Inputs) :
  R.v41043 (state s) (inputs i) = Zmod.unsigned (N.v41043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41043 s i)) at 1.
  unfold R.v41043, N.v41043.
  rewrite ?node_41041.
  rewrite ?node_41042.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41044 (s : N.State) (i : N.Inputs) :
  R.v41044 (state s) (inputs i) = Zmod.unsigned (N.v41044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41044 s i)) at 1.
  unfold R.v41044, N.v41044.
  unfold R.v16484, N.v16484.
  rewrite ?node_41043.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41045 (s : N.State) (i : N.Inputs) :
  R.v41045 (state s) (inputs i) = Zmod.unsigned (N.v41045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41045 s i)) at 1.
  unfold R.v41045, N.v41045.
  rewrite ?node_41040.
  rewrite ?node_41044.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41046 (s : N.State) (i : N.Inputs) :
  R.v41046 (state s) (inputs i) = Zmod.unsigned (N.v41046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41046 s i)) at 1.
  unfold R.v41046, N.v41046.
  unfold R.v6, N.v6.
  rewrite ?node_41045.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41047 (s : N.State) (i : N.Inputs) :
  R.v41047 (state s) (inputs i) = Zmod.unsigned (N.v41047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41047 s i)) at 1.
  unfold R.v41047, N.v41047.
  rewrite ?node_8492.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41048 (s : N.State) (i : N.Inputs) :
  R.v41048 (state s) (inputs i) = Zmod.unsigned (N.v41048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41048 s i)) at 1.
  unfold R.v41048, N.v41048.
  unfold R.v6, N.v6.
  rewrite ?node_8629.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41049 (s : N.State) (i : N.Inputs) :
  R.v41049 (state s) (inputs i) = Zmod.unsigned (N.v41049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41049 s i)) at 1.
  unfold R.v41049, N.v41049.
  rewrite ?node_41047.
  rewrite ?node_41048.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41050 (s : N.State) (i : N.Inputs) :
  R.v41050 (state s) (inputs i) = Zmod.unsigned (N.v41050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41050 s i)) at 1.
  unfold R.v41050, N.v41050.
  rewrite ?node_41046.
  rewrite ?node_41049.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41051 (s : N.State) (i : N.Inputs) :
  R.v41051 (state s) (inputs i) = Zmod.unsigned (N.v41051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41051 s i)) at 1.
  unfold R.v41051, N.v41051.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41052 (s : N.State) (i : N.Inputs) :
  R.v41052 (state s) (inputs i) = Zmod.unsigned (N.v41052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41052 s i)) at 1.
  unfold R.v41052, N.v41052.
  rewrite ?node_8499.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41053 (s : N.State) (i : N.Inputs) :
  R.v41053 (state s) (inputs i) = Zmod.unsigned (N.v41053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41053 s i)) at 1.
  unfold R.v41053, N.v41053.
  unfold R.v6, N.v6.
  rewrite ?node_8495.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41054 (s : N.State) (i : N.Inputs) :
  R.v41054 (state s) (inputs i) = Zmod.unsigned (N.v41054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41054 s i)) at 1.
  unfold R.v41054, N.v41054.
  unfold R.v6, N.v6.
  rewrite ?node_8492.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41055 (s : N.State) (i : N.Inputs) :
  R.v41055 (state s) (inputs i) = Zmod.unsigned (N.v41055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41055 s i)) at 1.
  unfold R.v41055, N.v41055.
  rewrite ?node_41053.
  rewrite ?node_41054.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41056 (s : N.State) (i : N.Inputs) :
  R.v41056 (state s) (inputs i) = Zmod.unsigned (N.v41056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41056 s i)) at 1.
  unfold R.v41056, N.v41056.
  unfold R.v16484, N.v16484.
  rewrite ?node_41055.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41057 (s : N.State) (i : N.Inputs) :
  R.v41057 (state s) (inputs i) = Zmod.unsigned (N.v41057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41057 s i)) at 1.
  unfold R.v41057, N.v41057.
  rewrite ?node_41052.
  rewrite ?node_41056.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41058 (s : N.State) (i : N.Inputs) :
  R.v41058 (state s) (inputs i) = Zmod.unsigned (N.v41058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41058 s i)) at 1.
  unfold R.v41058, N.v41058.
  unfold R.v6, N.v6.
  rewrite ?node_41057.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41059 (s : N.State) (i : N.Inputs) :
  R.v41059 (state s) (inputs i) = Zmod.unsigned (N.v41059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41059 s i)) at 1.
  unfold R.v41059, N.v41059.
  rewrite ?node_8500.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41060 (s : N.State) (i : N.Inputs) :
  R.v41060 (state s) (inputs i) = Zmod.unsigned (N.v41060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41060 s i)) at 1.
  unfold R.v41060, N.v41060.
  unfold R.v6, N.v6.
  rewrite ?node_8653.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41061 (s : N.State) (i : N.Inputs) :
  R.v41061 (state s) (inputs i) = Zmod.unsigned (N.v41061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41061 s i)) at 1.
  unfold R.v41061, N.v41061.
  rewrite ?node_41059.
  rewrite ?node_41060.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41062 (s : N.State) (i : N.Inputs) :
  R.v41062 (state s) (inputs i) = Zmod.unsigned (N.v41062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41062 s i)) at 1.
  unfold R.v41062, N.v41062.
  rewrite ?node_41058.
  rewrite ?node_41061.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41063 (s : N.State) (i : N.Inputs) :
  R.v41063 (state s) (inputs i) = Zmod.unsigned (N.v41063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41063 s i)) at 1.
  unfold R.v41063, N.v41063.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41064 (s : N.State) (i : N.Inputs) :
  R.v41064 (state s) (inputs i) = Zmod.unsigned (N.v41064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41064 s i)) at 1.
  unfold R.v41064, N.v41064.
  unfold R.v6, N.v6.
  rewrite ?node_8507.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41065 (s : N.State) (i : N.Inputs) :
  R.v41065 (state s) (inputs i) = Zmod.unsigned (N.v41065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41065 s i)) at 1.
  unfold R.v41065, N.v41065.
  unfold R.v6, N.v6.
  rewrite ?node_8504.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41066 (s : N.State) (i : N.Inputs) :
  R.v41066 (state s) (inputs i) = Zmod.unsigned (N.v41066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41066 s i)) at 1.
  unfold R.v41066, N.v41066.
  rewrite ?node_41064.
  rewrite ?node_41065.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41067 (s : N.State) (i : N.Inputs) :
  R.v41067 (state s) (inputs i) = Zmod.unsigned (N.v41067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41067 s i)) at 1.
  unfold R.v41067, N.v41067.
  unfold R.v16463, N.v16463.
  rewrite ?node_41066.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41068 (s : N.State) (i : N.Inputs) :
  R.v41068 (state s) (inputs i) = Zmod.unsigned (N.v41068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41068 s i)) at 1.
  unfold R.v41068, N.v41068.
  rewrite ?node_8508.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41069 (s : N.State) (i : N.Inputs) :
  R.v41069 (state s) (inputs i) = Zmod.unsigned (N.v41069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41069 s i)) at 1.
  unfold R.v41069, N.v41069.
  unfold R.v6, N.v6.
  rewrite ?node_8655.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41070 (s : N.State) (i : N.Inputs) :
  R.v41070 (state s) (inputs i) = Zmod.unsigned (N.v41070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41070 s i)) at 1.
  unfold R.v41070, N.v41070.
  rewrite ?node_41068.
  rewrite ?node_41069.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41071 (s : N.State) (i : N.Inputs) :
  R.v41071 (state s) (inputs i) = Zmod.unsigned (N.v41071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41071 s i)) at 1.
  unfold R.v41071, N.v41071.
  rewrite ?node_41067.
  rewrite ?node_41070.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41072 (s : N.State) (i : N.Inputs) :
  R.v41072 (state s) (inputs i) = Zmod.unsigned (N.v41072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41072 s i)) at 1.
  unfold R.v41072, N.v41072.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41073 (s : N.State) (i : N.Inputs) :
  R.v41073 (state s) (inputs i) = Zmod.unsigned (N.v41073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41073 s i)) at 1.
  unfold R.v41073, N.v41073.
  rewrite ?node_8582.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41074 (s : N.State) (i : N.Inputs) :
  R.v41074 (state s) (inputs i) = Zmod.unsigned (N.v41074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41074 s i)) at 1.
  unfold R.v41074, N.v41074.
  rewrite ?node_8578.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41075 (s : N.State) (i : N.Inputs) :
  R.v41075 (state s) (inputs i) = Zmod.unsigned (N.v41075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41075 s i)) at 1.
  unfold R.v41075, N.v41075.
  rewrite ?node_8570.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41076 (s : N.State) (i : N.Inputs) :
  R.v41076 (state s) (inputs i) = Zmod.unsigned (N.v41076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41076 s i)) at 1.
  unfold R.v41076, N.v41076.
  unfold R.v6, N.v6.
  rewrite ?node_8562.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41077 (s : N.State) (i : N.Inputs) :
  R.v41077 (state s) (inputs i) = Zmod.unsigned (N.v41077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41077 s i)) at 1.
  unfold R.v41077, N.v41077.
  unfold R.v6, N.v6.
  rewrite ?node_8555.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41078 (s : N.State) (i : N.Inputs) :
  R.v41078 (state s) (inputs i) = Zmod.unsigned (N.v41078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41078 s i)) at 1.
  unfold R.v41078, N.v41078.
  rewrite ?node_41076.
  rewrite ?node_41077.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41079 (s : N.State) (i : N.Inputs) :
  R.v41079 (state s) (inputs i) = Zmod.unsigned (N.v41079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41079 s i)) at 1.
  unfold R.v41079, N.v41079.
  unfold R.v16484, N.v16484.
  rewrite ?node_41078.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41080 (s : N.State) (i : N.Inputs) :
  R.v41080 (state s) (inputs i) = Zmod.unsigned (N.v41080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41080 s i)) at 1.
  unfold R.v41080, N.v41080.
  rewrite ?node_41073.
  rewrite ?node_41074.
  rewrite ?node_41075.
  rewrite ?node_41079.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41081 (s : N.State) (i : N.Inputs) :
  R.v41081 (state s) (inputs i) = Zmod.unsigned (N.v41081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41081 s i)) at 1.
  unfold R.v41081, N.v41081.
  unfold R.v6, N.v6.
  rewrite ?node_41080.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41082 (s : N.State) (i : N.Inputs) :
  R.v41082 (state s) (inputs i) = Zmod.unsigned (N.v41082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41082 s i)) at 1.
  unfold R.v41082, N.v41082.
  rewrite ?node_8583.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41083 (s : N.State) (i : N.Inputs) :
  R.v41083 (state s) (inputs i) = Zmod.unsigned (N.v41083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41083 s i)) at 1.
  unfold R.v41083, N.v41083.
  unfold R.v6, N.v6.
  rewrite ?node_8714.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41084 (s : N.State) (i : N.Inputs) :
  R.v41084 (state s) (inputs i) = Zmod.unsigned (N.v41084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41084 s i)) at 1.
  unfold R.v41084, N.v41084.
  unfold R.v6, N.v6.
  rewrite ?node_8780.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41085 (s : N.State) (i : N.Inputs) :
  R.v41085 (state s) (inputs i) = Zmod.unsigned (N.v41085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41085 s i)) at 1.
  unfold R.v41085, N.v41085.
  rewrite ?node_41082.
  rewrite ?node_41083.
  rewrite ?node_41084.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41086 (s : N.State) (i : N.Inputs) :
  R.v41086 (state s) (inputs i) = Zmod.unsigned (N.v41086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41086 s i)) at 1.
  unfold R.v41086, N.v41086.
  rewrite ?node_41081.
  rewrite ?node_41085.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41087 (s : N.State) (i : N.Inputs) :
  R.v41087 (state s) (inputs i) = Zmod.unsigned (N.v41087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41087 s i)) at 1.
  unfold R.v41087, N.v41087.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41088 (s : N.State) (i : N.Inputs) :
  R.v41088 (state s) (inputs i) = Zmod.unsigned (N.v41088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41088 s i)) at 1.
  unfold R.v41088, N.v41088.
  rewrite ?node_8570.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41089 (s : N.State) (i : N.Inputs) :
  R.v41089 (state s) (inputs i) = Zmod.unsigned (N.v41089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41089 s i)) at 1.
  unfold R.v41089, N.v41089.
  unfold R.v6, N.v6.
  rewrite ?node_8562.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41090 (s : N.State) (i : N.Inputs) :
  R.v41090 (state s) (inputs i) = Zmod.unsigned (N.v41090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41090 s i)) at 1.
  unfold R.v41090, N.v41090.
  unfold R.v6, N.v6.
  rewrite ?node_8555.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41091 (s : N.State) (i : N.Inputs) :
  R.v41091 (state s) (inputs i) = Zmod.unsigned (N.v41091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41091 s i)) at 1.
  unfold R.v41091, N.v41091.
  rewrite ?node_41089.
  rewrite ?node_41090.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41092 (s : N.State) (i : N.Inputs) :
  R.v41092 (state s) (inputs i) = Zmod.unsigned (N.v41092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41092 s i)) at 1.
  unfold R.v41092, N.v41092.
  unfold R.v16484, N.v16484.
  rewrite ?node_41091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41093 (s : N.State) (i : N.Inputs) :
  R.v41093 (state s) (inputs i) = Zmod.unsigned (N.v41093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41093 s i)) at 1.
  unfold R.v41093, N.v41093.
  rewrite ?node_41088.
  rewrite ?node_41092.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41094 (s : N.State) (i : N.Inputs) :
  R.v41094 (state s) (inputs i) = Zmod.unsigned (N.v41094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41094 s i)) at 1.
  unfold R.v41094, N.v41094.
  unfold R.v6, N.v6.
  rewrite ?node_41093.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41095 (s : N.State) (i : N.Inputs) :
  R.v41095 (state s) (inputs i) = Zmod.unsigned (N.v41095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41095 s i)) at 1.
  unfold R.v41095, N.v41095.
  rewrite ?node_8571.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41096 (s : N.State) (i : N.Inputs) :
  R.v41096 (state s) (inputs i) = Zmod.unsigned (N.v41096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41096 s i)) at 1.
  unfold R.v41096, N.v41096.
  unfold R.v6, N.v6.
  rewrite ?node_8714.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41097 (s : N.State) (i : N.Inputs) :
  R.v41097 (state s) (inputs i) = Zmod.unsigned (N.v41097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41097 s i)) at 1.
  unfold R.v41097, N.v41097.
  rewrite ?node_41095.
  rewrite ?node_41096.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41098 (s : N.State) (i : N.Inputs) :
  R.v41098 (state s) (inputs i) = Zmod.unsigned (N.v41098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41098 s i)) at 1.
  unfold R.v41098, N.v41098.
  rewrite ?node_41094.
  rewrite ?node_41097.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41099 (s : N.State) (i : N.Inputs) :
  R.v41099 (state s) (inputs i) = Zmod.unsigned (N.v41099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41099 s i)) at 1.
  unfold R.v41099, N.v41099.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41100 (s : N.State) (i : N.Inputs) :
  R.v41100 (state s) (inputs i) = Zmod.unsigned (N.v41100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41100 s i)) at 1.
  unfold R.v41100, N.v41100.
  rewrite ?node_8582.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41101 (s : N.State) (i : N.Inputs) :
  R.v41101 (state s) (inputs i) = Zmod.unsigned (N.v41101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41101 s i)) at 1.
  unfold R.v41101, N.v41101.
  unfold R.v6, N.v6.
  rewrite ?node_8578.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41102 (s : N.State) (i : N.Inputs) :
  R.v41102 (state s) (inputs i) = Zmod.unsigned (N.v41102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41102 s i)) at 1.
  unfold R.v41102, N.v41102.
  unfold R.v6, N.v6.
  rewrite ?node_8571.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41103 (s : N.State) (i : N.Inputs) :
  R.v41103 (state s) (inputs i) = Zmod.unsigned (N.v41103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41103 s i)) at 1.
  unfold R.v41103, N.v41103.
  rewrite ?node_41101.
  rewrite ?node_41102.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41104 (s : N.State) (i : N.Inputs) :
  R.v41104 (state s) (inputs i) = Zmod.unsigned (N.v41104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41104 s i)) at 1.
  unfold R.v41104, N.v41104.
  unfold R.v16484, N.v16484.
  rewrite ?node_41103.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41105 (s : N.State) (i : N.Inputs) :
  R.v41105 (state s) (inputs i) = Zmod.unsigned (N.v41105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41105 s i)) at 1.
  unfold R.v41105, N.v41105.
  rewrite ?node_41100.
  rewrite ?node_41104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41106 (s : N.State) (i : N.Inputs) :
  R.v41106 (state s) (inputs i) = Zmod.unsigned (N.v41106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41106 s i)) at 1.
  unfold R.v41106, N.v41106.
  unfold R.v6, N.v6.
  rewrite ?node_41105.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41107 (s : N.State) (i : N.Inputs) :
  R.v41107 (state s) (inputs i) = Zmod.unsigned (N.v41107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41107 s i)) at 1.
  unfold R.v41107, N.v41107.
  rewrite ?node_8583.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41108 (s : N.State) (i : N.Inputs) :
  R.v41108 (state s) (inputs i) = Zmod.unsigned (N.v41108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41108 s i)) at 1.
  unfold R.v41108, N.v41108.
  unfold R.v6, N.v6.
  rewrite ?node_8780.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41109 (s : N.State) (i : N.Inputs) :
  R.v41109 (state s) (inputs i) = Zmod.unsigned (N.v41109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41109 s i)) at 1.
  unfold R.v41109, N.v41109.
  rewrite ?node_41107.
  rewrite ?node_41108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41110 (s : N.State) (i : N.Inputs) :
  R.v41110 (state s) (inputs i) = Zmod.unsigned (N.v41110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41110 s i)) at 1.
  unfold R.v41110, N.v41110.
  rewrite ?node_41106.
  rewrite ?node_41109.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41111 (s : N.State) (i : N.Inputs) :
  R.v41111 (state s) (inputs i) = Zmod.unsigned (N.v41111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41111 s i)) at 1.
  unfold R.v41111, N.v41111.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41112 (s : N.State) (i : N.Inputs) :
  R.v41112 (state s) (inputs i) = Zmod.unsigned (N.v41112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41112 s i)) at 1.
  unfold R.v41112, N.v41112.
  rewrite ?node_8609.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41113 (s : N.State) (i : N.Inputs) :
  R.v41113 (state s) (inputs i) = Zmod.unsigned (N.v41113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41113 s i)) at 1.
  unfold R.v41113, N.v41113.
  rewrite ?node_8605.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41114 (s : N.State) (i : N.Inputs) :
  R.v41114 (state s) (inputs i) = Zmod.unsigned (N.v41114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41114 s i)) at 1.
  unfold R.v41114, N.v41114.
  rewrite ?node_8601.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41115 (s : N.State) (i : N.Inputs) :
  R.v41115 (state s) (inputs i) = Zmod.unsigned (N.v41115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41115 s i)) at 1.
  unfold R.v41115, N.v41115.
  unfold R.v6, N.v6.
  rewrite ?node_8597.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41116 (s : N.State) (i : N.Inputs) :
  R.v41116 (state s) (inputs i) = Zmod.unsigned (N.v41116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41116 s i)) at 1.
  unfold R.v41116, N.v41116.
  unfold R.v6, N.v6.
  rewrite ?node_8590.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41117 (s : N.State) (i : N.Inputs) :
  R.v41117 (state s) (inputs i) = Zmod.unsigned (N.v41117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41117 s i)) at 1.
  unfold R.v41117, N.v41117.
  rewrite ?node_41115.
  rewrite ?node_41116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41118 (s : N.State) (i : N.Inputs) :
  R.v41118 (state s) (inputs i) = Zmod.unsigned (N.v41118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41118 s i)) at 1.
  unfold R.v41118, N.v41118.
  unfold R.v16484, N.v16484.
  rewrite ?node_41117.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41119 (s : N.State) (i : N.Inputs) :
  R.v41119 (state s) (inputs i) = Zmod.unsigned (N.v41119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41119 s i)) at 1.
  unfold R.v41119, N.v41119.
  rewrite ?node_41112.
  rewrite ?node_41113.
  rewrite ?node_41114.
  rewrite ?node_41118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41120 (s : N.State) (i : N.Inputs) :
  R.v41120 (state s) (inputs i) = Zmod.unsigned (N.v41120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41120 s i)) at 1.
  unfold R.v41120, N.v41120.
  unfold R.v6, N.v6.
  rewrite ?node_41119.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41121 (s : N.State) (i : N.Inputs) :
  R.v41121 (state s) (inputs i) = Zmod.unsigned (N.v41121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41121 s i)) at 1.
  unfold R.v41121, N.v41121.
  rewrite ?node_8610.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41122 (s : N.State) (i : N.Inputs) :
  R.v41122 (state s) (inputs i) = Zmod.unsigned (N.v41122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41122 s i)) at 1.
  unfold R.v41122, N.v41122.
  unfold R.v6, N.v6.
  rewrite ?node_8745.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41123 (s : N.State) (i : N.Inputs) :
  R.v41123 (state s) (inputs i) = Zmod.unsigned (N.v41123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41123 s i)) at 1.
  unfold R.v41123, N.v41123.
  unfold R.v6, N.v6.
  rewrite ?node_8783.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41124 (s : N.State) (i : N.Inputs) :
  R.v41124 (state s) (inputs i) = Zmod.unsigned (N.v41124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41124 s i)) at 1.
  unfold R.v41124, N.v41124.
  rewrite ?node_41121.
  rewrite ?node_41122.
  rewrite ?node_41123.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41125 (s : N.State) (i : N.Inputs) :
  R.v41125 (state s) (inputs i) = Zmod.unsigned (N.v41125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41125 s i)) at 1.
  unfold R.v41125, N.v41125.
  rewrite ?node_41120.
  rewrite ?node_41124.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41126 (s : N.State) (i : N.Inputs) :
  R.v41126 (state s) (inputs i) = Zmod.unsigned (N.v41126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41126 s i)) at 1.
  unfold R.v41126, N.v41126.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41127 (s : N.State) (i : N.Inputs) :
  R.v41127 (state s) (inputs i) = Zmod.unsigned (N.v41127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41127 s i)) at 1.
  unfold R.v41127, N.v41127.
  rewrite ?node_8601.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41128 (s : N.State) (i : N.Inputs) :
  R.v41128 (state s) (inputs i) = Zmod.unsigned (N.v41128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41128 s i)) at 1.
  unfold R.v41128, N.v41128.
  unfold R.v6, N.v6.
  rewrite ?node_8597.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41129 (s : N.State) (i : N.Inputs) :
  R.v41129 (state s) (inputs i) = Zmod.unsigned (N.v41129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41129 s i)) at 1.
  unfold R.v41129, N.v41129.
  unfold R.v6, N.v6.
  rewrite ?node_8590.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41130 (s : N.State) (i : N.Inputs) :
  R.v41130 (state s) (inputs i) = Zmod.unsigned (N.v41130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41130 s i)) at 1.
  unfold R.v41130, N.v41130.
  rewrite ?node_41128.
  rewrite ?node_41129.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41131 (s : N.State) (i : N.Inputs) :
  R.v41131 (state s) (inputs i) = Zmod.unsigned (N.v41131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41131 s i)) at 1.
  unfold R.v41131, N.v41131.
  unfold R.v16484, N.v16484.
  rewrite ?node_41130.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41132 (s : N.State) (i : N.Inputs) :
  R.v41132 (state s) (inputs i) = Zmod.unsigned (N.v41132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41132 s i)) at 1.
  unfold R.v41132, N.v41132.
  rewrite ?node_41127.
  rewrite ?node_41131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41133 (s : N.State) (i : N.Inputs) :
  R.v41133 (state s) (inputs i) = Zmod.unsigned (N.v41133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41133 s i)) at 1.
  unfold R.v41133, N.v41133.
  unfold R.v6, N.v6.
  rewrite ?node_41132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41134 (s : N.State) (i : N.Inputs) :
  R.v41134 (state s) (inputs i) = Zmod.unsigned (N.v41134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41134 s i)) at 1.
  unfold R.v41134, N.v41134.
  rewrite ?node_8602.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41135 (s : N.State) (i : N.Inputs) :
  R.v41135 (state s) (inputs i) = Zmod.unsigned (N.v41135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41135 s i)) at 1.
  unfold R.v41135, N.v41135.
  unfold R.v6, N.v6.
  rewrite ?node_8745.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41136 (s : N.State) (i : N.Inputs) :
  R.v41136 (state s) (inputs i) = Zmod.unsigned (N.v41136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41136 s i)) at 1.
  unfold R.v41136, N.v41136.
  rewrite ?node_41134.
  rewrite ?node_41135.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41137 (s : N.State) (i : N.Inputs) :
  R.v41137 (state s) (inputs i) = Zmod.unsigned (N.v41137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41137 s i)) at 1.
  unfold R.v41137, N.v41137.
  rewrite ?node_41133.
  rewrite ?node_41136.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41138 (s : N.State) (i : N.Inputs) :
  R.v41138 (state s) (inputs i) = Zmod.unsigned (N.v41138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41138 s i)) at 1.
  unfold R.v41138, N.v41138.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41139 (s : N.State) (i : N.Inputs) :
  R.v41139 (state s) (inputs i) = Zmod.unsigned (N.v41139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41139 s i)) at 1.
  unfold R.v41139, N.v41139.
  rewrite ?node_8609.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41140 (s : N.State) (i : N.Inputs) :
  R.v41140 (state s) (inputs i) = Zmod.unsigned (N.v41140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41140 s i)) at 1.
  unfold R.v41140, N.v41140.
  unfold R.v6, N.v6.
  rewrite ?node_8605.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41141 (s : N.State) (i : N.Inputs) :
  R.v41141 (state s) (inputs i) = Zmod.unsigned (N.v41141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41141 s i)) at 1.
  unfold R.v41141, N.v41141.
  unfold R.v6, N.v6.
  rewrite ?node_8602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41142 (s : N.State) (i : N.Inputs) :
  R.v41142 (state s) (inputs i) = Zmod.unsigned (N.v41142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41142 s i)) at 1.
  unfold R.v41142, N.v41142.
  rewrite ?node_41140.
  rewrite ?node_41141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41143 (s : N.State) (i : N.Inputs) :
  R.v41143 (state s) (inputs i) = Zmod.unsigned (N.v41143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41143 s i)) at 1.
  unfold R.v41143, N.v41143.
  unfold R.v16484, N.v16484.
  rewrite ?node_41142.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41144 (s : N.State) (i : N.Inputs) :
  R.v41144 (state s) (inputs i) = Zmod.unsigned (N.v41144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41144 s i)) at 1.
  unfold R.v41144, N.v41144.
  rewrite ?node_41139.
  rewrite ?node_41143.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41145 (s : N.State) (i : N.Inputs) :
  R.v41145 (state s) (inputs i) = Zmod.unsigned (N.v41145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41145 s i)) at 1.
  unfold R.v41145, N.v41145.
  unfold R.v6, N.v6.
  rewrite ?node_41144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41146 (s : N.State) (i : N.Inputs) :
  R.v41146 (state s) (inputs i) = Zmod.unsigned (N.v41146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41146 s i)) at 1.
  unfold R.v41146, N.v41146.
  rewrite ?node_8610.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41147 (s : N.State) (i : N.Inputs) :
  R.v41147 (state s) (inputs i) = Zmod.unsigned (N.v41147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41147 s i)) at 1.
  unfold R.v41147, N.v41147.
  unfold R.v6, N.v6.
  rewrite ?node_8783.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41148 (s : N.State) (i : N.Inputs) :
  R.v41148 (state s) (inputs i) = Zmod.unsigned (N.v41148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41148 s i)) at 1.
  unfold R.v41148, N.v41148.
  rewrite ?node_41146.
  rewrite ?node_41147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41149 (s : N.State) (i : N.Inputs) :
  R.v41149 (state s) (inputs i) = Zmod.unsigned (N.v41149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41149 s i)) at 1.
  unfold R.v41149, N.v41149.
  rewrite ?node_41145.
  rewrite ?node_41148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41150 (s : N.State) (i : N.Inputs) :
  R.v41150 (state s) (inputs i) = Zmod.unsigned (N.v41150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41150 s i)) at 1.
  unfold R.v41150, N.v41150.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41151 (s : N.State) (i : N.Inputs) :
  R.v41151 (state s) (inputs i) = Zmod.unsigned (N.v41151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41151 s i)) at 1.
  unfold R.v41151, N.v41151.
  rewrite ?node_8629.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41152 (s : N.State) (i : N.Inputs) :
  R.v41152 (state s) (inputs i) = Zmod.unsigned (N.v41152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41152 s i)) at 1.
  unfold R.v41152, N.v41152.
  rewrite ?node_8625.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41153 (s : N.State) (i : N.Inputs) :
  R.v41153 (state s) (inputs i) = Zmod.unsigned (N.v41153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41153 s i)) at 1.
  unfold R.v41153, N.v41153.
  rewrite ?node_8621.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41154 (s : N.State) (i : N.Inputs) :
  R.v41154 (state s) (inputs i) = Zmod.unsigned (N.v41154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41154 s i)) at 1.
  unfold R.v41154, N.v41154.
  unfold R.v6, N.v6.
  rewrite ?node_8617.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41155 (s : N.State) (i : N.Inputs) :
  R.v41155 (state s) (inputs i) = Zmod.unsigned (N.v41155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41155 s i)) at 1.
  unfold R.v41155, N.v41155.
  unfold R.v6, N.v6.
  rewrite ?node_8614.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41156 (s : N.State) (i : N.Inputs) :
  R.v41156 (state s) (inputs i) = Zmod.unsigned (N.v41156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41156 s i)) at 1.
  unfold R.v41156, N.v41156.
  rewrite ?node_41154.
  rewrite ?node_41155.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41157 (s : N.State) (i : N.Inputs) :
  R.v41157 (state s) (inputs i) = Zmod.unsigned (N.v41157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41157 s i)) at 1.
  unfold R.v41157, N.v41157.
  unfold R.v16484, N.v16484.
  rewrite ?node_41156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41158 (s : N.State) (i : N.Inputs) :
  R.v41158 (state s) (inputs i) = Zmod.unsigned (N.v41158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41158 s i)) at 1.
  unfold R.v41158, N.v41158.
  rewrite ?node_41151.
  rewrite ?node_41152.
  rewrite ?node_41153.
  rewrite ?node_41157.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41159 (s : N.State) (i : N.Inputs) :
  R.v41159 (state s) (inputs i) = Zmod.unsigned (N.v41159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41159 s i)) at 1.
  unfold R.v41159, N.v41159.
  unfold R.v6, N.v6.
  rewrite ?node_41158.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41160 (s : N.State) (i : N.Inputs) :
  R.v41160 (state s) (inputs i) = Zmod.unsigned (N.v41160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41160 s i)) at 1.
  unfold R.v41160, N.v41160.
  rewrite ?node_8630.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41161 (s : N.State) (i : N.Inputs) :
  R.v41161 (state s) (inputs i) = Zmod.unsigned (N.v41161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41161 s i)) at 1.
  unfold R.v41161, N.v41161.
  unfold R.v6, N.v6.
  rewrite ?node_8765.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41162 (s : N.State) (i : N.Inputs) :
  R.v41162 (state s) (inputs i) = Zmod.unsigned (N.v41162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41162 s i)) at 1.
  unfold R.v41162, N.v41162.
  unfold R.v6, N.v6.
  rewrite ?node_8787.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41163 (s : N.State) (i : N.Inputs) :
  R.v41163 (state s) (inputs i) = Zmod.unsigned (N.v41163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41163 s i)) at 1.
  unfold R.v41163, N.v41163.
  rewrite ?node_41160.
  rewrite ?node_41161.
  rewrite ?node_41162.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41164 (s : N.State) (i : N.Inputs) :
  R.v41164 (state s) (inputs i) = Zmod.unsigned (N.v41164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41164 s i)) at 1.
  unfold R.v41164, N.v41164.
  rewrite ?node_41159.
  rewrite ?node_41163.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41165 (s : N.State) (i : N.Inputs) :
  R.v41165 (state s) (inputs i) = Zmod.unsigned (N.v41165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41165 s i)) at 1.
  unfold R.v41165, N.v41165.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41166 (s : N.State) (i : N.Inputs) :
  R.v41166 (state s) (inputs i) = Zmod.unsigned (N.v41166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41166 s i)) at 1.
  unfold R.v41166, N.v41166.
  rewrite ?node_8621.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41167 (s : N.State) (i : N.Inputs) :
  R.v41167 (state s) (inputs i) = Zmod.unsigned (N.v41167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41167 s i)) at 1.
  unfold R.v41167, N.v41167.
  unfold R.v6, N.v6.
  rewrite ?node_8617.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41168 (s : N.State) (i : N.Inputs) :
  R.v41168 (state s) (inputs i) = Zmod.unsigned (N.v41168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41168 s i)) at 1.
  unfold R.v41168, N.v41168.
  unfold R.v6, N.v6.
  rewrite ?node_8614.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41169 (s : N.State) (i : N.Inputs) :
  R.v41169 (state s) (inputs i) = Zmod.unsigned (N.v41169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41169 s i)) at 1.
  unfold R.v41169, N.v41169.
  rewrite ?node_41167.
  rewrite ?node_41168.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41170 (s : N.State) (i : N.Inputs) :
  R.v41170 (state s) (inputs i) = Zmod.unsigned (N.v41170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41170 s i)) at 1.
  unfold R.v41170, N.v41170.
  unfold R.v16484, N.v16484.
  rewrite ?node_41169.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41171 (s : N.State) (i : N.Inputs) :
  R.v41171 (state s) (inputs i) = Zmod.unsigned (N.v41171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41171 s i)) at 1.
  unfold R.v41171, N.v41171.
  rewrite ?node_41166.
  rewrite ?node_41170.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41172 (s : N.State) (i : N.Inputs) :
  R.v41172 (state s) (inputs i) = Zmod.unsigned (N.v41172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41172 s i)) at 1.
  unfold R.v41172, N.v41172.
  unfold R.v6, N.v6.
  rewrite ?node_41171.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41173 (s : N.State) (i : N.Inputs) :
  R.v41173 (state s) (inputs i) = Zmod.unsigned (N.v41173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41173 s i)) at 1.
  unfold R.v41173, N.v41173.
  rewrite ?node_8622.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41174 (s : N.State) (i : N.Inputs) :
  R.v41174 (state s) (inputs i) = Zmod.unsigned (N.v41174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41174 s i)) at 1.
  unfold R.v41174, N.v41174.
  unfold R.v6, N.v6.
  rewrite ?node_8765.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41175 (s : N.State) (i : N.Inputs) :
  R.v41175 (state s) (inputs i) = Zmod.unsigned (N.v41175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41175 s i)) at 1.
  unfold R.v41175, N.v41175.
  rewrite ?node_41173.
  rewrite ?node_41174.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41176 (s : N.State) (i : N.Inputs) :
  R.v41176 (state s) (inputs i) = Zmod.unsigned (N.v41176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41176 s i)) at 1.
  unfold R.v41176, N.v41176.
  rewrite ?node_41172.
  rewrite ?node_41175.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41177 (s : N.State) (i : N.Inputs) :
  R.v41177 (state s) (inputs i) = Zmod.unsigned (N.v41177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41177 s i)) at 1.
  unfold R.v41177, N.v41177.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41178 (s : N.State) (i : N.Inputs) :
  R.v41178 (state s) (inputs i) = Zmod.unsigned (N.v41178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41178 s i)) at 1.
  unfold R.v41178, N.v41178.
  rewrite ?node_8629.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41179 (s : N.State) (i : N.Inputs) :
  R.v41179 (state s) (inputs i) = Zmod.unsigned (N.v41179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41179 s i)) at 1.
  unfold R.v41179, N.v41179.
  unfold R.v6, N.v6.
  rewrite ?node_8625.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41180 (s : N.State) (i : N.Inputs) :
  R.v41180 (state s) (inputs i) = Zmod.unsigned (N.v41180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41180 s i)) at 1.
  unfold R.v41180, N.v41180.
  unfold R.v6, N.v6.
  rewrite ?node_8622.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41181 (s : N.State) (i : N.Inputs) :
  R.v41181 (state s) (inputs i) = Zmod.unsigned (N.v41181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41181 s i)) at 1.
  unfold R.v41181, N.v41181.
  rewrite ?node_41179.
  rewrite ?node_41180.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41182 (s : N.State) (i : N.Inputs) :
  R.v41182 (state s) (inputs i) = Zmod.unsigned (N.v41182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41182 s i)) at 1.
  unfold R.v41182, N.v41182.
  unfold R.v16484, N.v16484.
  rewrite ?node_41181.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41183 (s : N.State) (i : N.Inputs) :
  R.v41183 (state s) (inputs i) = Zmod.unsigned (N.v41183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41183 s i)) at 1.
  unfold R.v41183, N.v41183.
  rewrite ?node_41178.
  rewrite ?node_41182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41184 (s : N.State) (i : N.Inputs) :
  R.v41184 (state s) (inputs i) = Zmod.unsigned (N.v41184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41184 s i)) at 1.
  unfold R.v41184, N.v41184.
  unfold R.v6, N.v6.
  rewrite ?node_41183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41185 (s : N.State) (i : N.Inputs) :
  R.v41185 (state s) (inputs i) = Zmod.unsigned (N.v41185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41185 s i)) at 1.
  unfold R.v41185, N.v41185.
  rewrite ?node_8630.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41186 (s : N.State) (i : N.Inputs) :
  R.v41186 (state s) (inputs i) = Zmod.unsigned (N.v41186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41186 s i)) at 1.
  unfold R.v41186, N.v41186.
  unfold R.v6, N.v6.
  rewrite ?node_8787.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41187 (s : N.State) (i : N.Inputs) :
  R.v41187 (state s) (inputs i) = Zmod.unsigned (N.v41187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41187 s i)) at 1.
  unfold R.v41187, N.v41187.
  rewrite ?node_41185.
  rewrite ?node_41186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41188 (s : N.State) (i : N.Inputs) :
  R.v41188 (state s) (inputs i) = Zmod.unsigned (N.v41188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41188 s i)) at 1.
  unfold R.v41188, N.v41188.
  rewrite ?node_41184.
  rewrite ?node_41187.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41189 (s : N.State) (i : N.Inputs) :
  R.v41189 (state s) (inputs i) = Zmod.unsigned (N.v41189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41189 s i)) at 1.
  unfold R.v41189, N.v41189.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41190 (s : N.State) (i : N.Inputs) :
  R.v41190 (state s) (inputs i) = Zmod.unsigned (N.v41190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41190 s i)) at 1.
  unfold R.v41190, N.v41190.
  unfold R.v6, N.v6.
  rewrite ?node_8637.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41191 (s : N.State) (i : N.Inputs) :
  R.v41191 (state s) (inputs i) = Zmod.unsigned (N.v41191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41191 s i)) at 1.
  unfold R.v41191, N.v41191.
  unfold R.v6, N.v6.
  rewrite ?node_8634.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41192 (s : N.State) (i : N.Inputs) :
  R.v41192 (state s) (inputs i) = Zmod.unsigned (N.v41192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41192 s i)) at 1.
  unfold R.v41192, N.v41192.
  rewrite ?node_41190.
  rewrite ?node_41191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41193 (s : N.State) (i : N.Inputs) :
  R.v41193 (state s) (inputs i) = Zmod.unsigned (N.v41193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41193 s i)) at 1.
  unfold R.v41193, N.v41193.
  unfold R.v16463, N.v16463.
  rewrite ?node_41192.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41194 (s : N.State) (i : N.Inputs) :
  R.v41194 (state s) (inputs i) = Zmod.unsigned (N.v41194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41194 s i)) at 1.
  unfold R.v41194, N.v41194.
  rewrite ?node_8638.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41195 (s : N.State) (i : N.Inputs) :
  R.v41195 (state s) (inputs i) = Zmod.unsigned (N.v41195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41195 s i)) at 1.
  unfold R.v41195, N.v41195.
  unfold R.v6, N.v6.
  rewrite ?node_8789.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41196 (s : N.State) (i : N.Inputs) :
  R.v41196 (state s) (inputs i) = Zmod.unsigned (N.v41196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41196 s i)) at 1.
  unfold R.v41196, N.v41196.
  rewrite ?node_41194.
  rewrite ?node_41195.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41197 (s : N.State) (i : N.Inputs) :
  R.v41197 (state s) (inputs i) = Zmod.unsigned (N.v41197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41197 s i)) at 1.
  unfold R.v41197, N.v41197.
  rewrite ?node_41193.
  rewrite ?node_41196.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41198 (s : N.State) (i : N.Inputs) :
  R.v41198 (state s) (inputs i) = Zmod.unsigned (N.v41198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41198 s i)) at 1.
  unfold R.v41198, N.v41198.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41199 (s : N.State) (i : N.Inputs) :
  R.v41199 (state s) (inputs i) = Zmod.unsigned (N.v41199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41199 s i)) at 1.
  unfold R.v41199, N.v41199.
  rewrite ?node_8714.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41200 (s : N.State) (i : N.Inputs) :
  R.v41200 (state s) (inputs i) = Zmod.unsigned (N.v41200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41200 s i)) at 1.
  unfold R.v41200, N.v41200.
  rewrite ?node_8710.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41201 (s : N.State) (i : N.Inputs) :
  R.v41201 (state s) (inputs i) = Zmod.unsigned (N.v41201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41201 s i)) at 1.
  unfold R.v41201, N.v41201.
  rewrite ?node_8702.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41202 (s : N.State) (i : N.Inputs) :
  R.v41202 (state s) (inputs i) = Zmod.unsigned (N.v41202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41202 s i)) at 1.
  unfold R.v41202, N.v41202.
  unfold R.v6, N.v6.
  rewrite ?node_8694.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41203 (s : N.State) (i : N.Inputs) :
  R.v41203 (state s) (inputs i) = Zmod.unsigned (N.v41203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41203 s i)) at 1.
  unfold R.v41203, N.v41203.
  unfold R.v6, N.v6.
  rewrite ?node_8687.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41204 (s : N.State) (i : N.Inputs) :
  R.v41204 (state s) (inputs i) = Zmod.unsigned (N.v41204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41204 s i)) at 1.
  unfold R.v41204, N.v41204.
  rewrite ?node_41202.
  rewrite ?node_41203.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41205 (s : N.State) (i : N.Inputs) :
  R.v41205 (state s) (inputs i) = Zmod.unsigned (N.v41205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41205 s i)) at 1.
  unfold R.v41205, N.v41205.
  unfold R.v16484, N.v16484.
  rewrite ?node_41204.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41206 (s : N.State) (i : N.Inputs) :
  R.v41206 (state s) (inputs i) = Zmod.unsigned (N.v41206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41206 s i)) at 1.
  unfold R.v41206, N.v41206.
  rewrite ?node_41199.
  rewrite ?node_41200.
  rewrite ?node_41201.
  rewrite ?node_41205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41207 (s : N.State) (i : N.Inputs) :
  R.v41207 (state s) (inputs i) = Zmod.unsigned (N.v41207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41207 s i)) at 1.
  unfold R.v41207, N.v41207.
  unfold R.v6, N.v6.
  rewrite ?node_41206.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41208 (s : N.State) (i : N.Inputs) :
  R.v41208 (state s) (inputs i) = Zmod.unsigned (N.v41208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41208 s i)) at 1.
  unfold R.v41208, N.v41208.
  rewrite ?node_8715.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41209 (s : N.State) (i : N.Inputs) :
  R.v41209 (state s) (inputs i) = Zmod.unsigned (N.v41209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41209 s i)) at 1.
  unfold R.v41209, N.v41209.
  unfold R.v6, N.v6.
  rewrite ?node_8848.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41210 (s : N.State) (i : N.Inputs) :
  R.v41210 (state s) (inputs i) = Zmod.unsigned (N.v41210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41210 s i)) at 1.
  unfold R.v41210, N.v41210.
  unfold R.v6, N.v6.
  rewrite ?node_8917.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41211 (s : N.State) (i : N.Inputs) :
  R.v41211 (state s) (inputs i) = Zmod.unsigned (N.v41211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41211 s i)) at 1.
  unfold R.v41211, N.v41211.
  rewrite ?node_41208.
  rewrite ?node_41209.
  rewrite ?node_41210.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41212 (s : N.State) (i : N.Inputs) :
  R.v41212 (state s) (inputs i) = Zmod.unsigned (N.v41212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41212 s i)) at 1.
  unfold R.v41212, N.v41212.
  rewrite ?node_41207.
  rewrite ?node_41211.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41213 (s : N.State) (i : N.Inputs) :
  R.v41213 (state s) (inputs i) = Zmod.unsigned (N.v41213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41213 s i)) at 1.
  unfold R.v41213, N.v41213.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41214 (s : N.State) (i : N.Inputs) :
  R.v41214 (state s) (inputs i) = Zmod.unsigned (N.v41214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41214 s i)) at 1.
  unfold R.v41214, N.v41214.
  rewrite ?node_8702.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41215 (s : N.State) (i : N.Inputs) :
  R.v41215 (state s) (inputs i) = Zmod.unsigned (N.v41215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41215 s i)) at 1.
  unfold R.v41215, N.v41215.
  unfold R.v6, N.v6.
  rewrite ?node_8694.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41216 (s : N.State) (i : N.Inputs) :
  R.v41216 (state s) (inputs i) = Zmod.unsigned (N.v41216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41216 s i)) at 1.
  unfold R.v41216, N.v41216.
  unfold R.v6, N.v6.
  rewrite ?node_8687.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41217 (s : N.State) (i : N.Inputs) :
  R.v41217 (state s) (inputs i) = Zmod.unsigned (N.v41217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41217 s i)) at 1.
  unfold R.v41217, N.v41217.
  rewrite ?node_41215.
  rewrite ?node_41216.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41218 (s : N.State) (i : N.Inputs) :
  R.v41218 (state s) (inputs i) = Zmod.unsigned (N.v41218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41218 s i)) at 1.
  unfold R.v41218, N.v41218.
  unfold R.v16484, N.v16484.
  rewrite ?node_41217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41219 (s : N.State) (i : N.Inputs) :
  R.v41219 (state s) (inputs i) = Zmod.unsigned (N.v41219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41219 s i)) at 1.
  unfold R.v41219, N.v41219.
  rewrite ?node_41214.
  rewrite ?node_41218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41220 (s : N.State) (i : N.Inputs) :
  R.v41220 (state s) (inputs i) = Zmod.unsigned (N.v41220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41220 s i)) at 1.
  unfold R.v41220, N.v41220.
  unfold R.v6, N.v6.
  rewrite ?node_41219.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41221 (s : N.State) (i : N.Inputs) :
  R.v41221 (state s) (inputs i) = Zmod.unsigned (N.v41221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41221 s i)) at 1.
  unfold R.v41221, N.v41221.
  rewrite ?node_8703.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41222 (s : N.State) (i : N.Inputs) :
  R.v41222 (state s) (inputs i) = Zmod.unsigned (N.v41222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41222 s i)) at 1.
  unfold R.v41222, N.v41222.
  unfold R.v6, N.v6.
  rewrite ?node_8848.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41223 (s : N.State) (i : N.Inputs) :
  R.v41223 (state s) (inputs i) = Zmod.unsigned (N.v41223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41223 s i)) at 1.
  unfold R.v41223, N.v41223.
  rewrite ?node_41221.
  rewrite ?node_41222.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41224 (s : N.State) (i : N.Inputs) :
  R.v41224 (state s) (inputs i) = Zmod.unsigned (N.v41224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41224 s i)) at 1.
  unfold R.v41224, N.v41224.
  rewrite ?node_41220.
  rewrite ?node_41223.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41225 (s : N.State) (i : N.Inputs) :
  R.v41225 (state s) (inputs i) = Zmod.unsigned (N.v41225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41225 s i)) at 1.
  unfold R.v41225, N.v41225.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41226 (s : N.State) (i : N.Inputs) :
  R.v41226 (state s) (inputs i) = Zmod.unsigned (N.v41226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41226 s i)) at 1.
  unfold R.v41226, N.v41226.
  rewrite ?node_8714.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41227 (s : N.State) (i : N.Inputs) :
  R.v41227 (state s) (inputs i) = Zmod.unsigned (N.v41227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41227 s i)) at 1.
  unfold R.v41227, N.v41227.
  unfold R.v6, N.v6.
  rewrite ?node_8710.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41228 (s : N.State) (i : N.Inputs) :
  R.v41228 (state s) (inputs i) = Zmod.unsigned (N.v41228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41228 s i)) at 1.
  unfold R.v41228, N.v41228.
  unfold R.v6, N.v6.
  rewrite ?node_8703.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41229 (s : N.State) (i : N.Inputs) :
  R.v41229 (state s) (inputs i) = Zmod.unsigned (N.v41229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41229 s i)) at 1.
  unfold R.v41229, N.v41229.
  rewrite ?node_41227.
  rewrite ?node_41228.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41230 (s : N.State) (i : N.Inputs) :
  R.v41230 (state s) (inputs i) = Zmod.unsigned (N.v41230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41230 s i)) at 1.
  unfold R.v41230, N.v41230.
  unfold R.v16484, N.v16484.
  rewrite ?node_41229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41231 (s : N.State) (i : N.Inputs) :
  R.v41231 (state s) (inputs i) = Zmod.unsigned (N.v41231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41231 s i)) at 1.
  unfold R.v41231, N.v41231.
  rewrite ?node_41226.
  rewrite ?node_41230.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41232 (s : N.State) (i : N.Inputs) :
  R.v41232 (state s) (inputs i) = Zmod.unsigned (N.v41232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41232 s i)) at 1.
  unfold R.v41232, N.v41232.
  unfold R.v6, N.v6.
  rewrite ?node_41231.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41233 (s : N.State) (i : N.Inputs) :
  R.v41233 (state s) (inputs i) = Zmod.unsigned (N.v41233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41233 s i)) at 1.
  unfold R.v41233, N.v41233.
  rewrite ?node_8715.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41234 (s : N.State) (i : N.Inputs) :
  R.v41234 (state s) (inputs i) = Zmod.unsigned (N.v41234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41234 s i)) at 1.
  unfold R.v41234, N.v41234.
  unfold R.v6, N.v6.
  rewrite ?node_8917.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41235 (s : N.State) (i : N.Inputs) :
  R.v41235 (state s) (inputs i) = Zmod.unsigned (N.v41235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41235 s i)) at 1.
  unfold R.v41235, N.v41235.
  rewrite ?node_41233.
  rewrite ?node_41234.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41236 (s : N.State) (i : N.Inputs) :
  R.v41236 (state s) (inputs i) = Zmod.unsigned (N.v41236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41236 s i)) at 1.
  unfold R.v41236, N.v41236.
  rewrite ?node_41232.
  rewrite ?node_41235.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41237 (s : N.State) (i : N.Inputs) :
  R.v41237 (state s) (inputs i) = Zmod.unsigned (N.v41237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41237 s i)) at 1.
  unfold R.v41237, N.v41237.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41238 (s : N.State) (i : N.Inputs) :
  R.v41238 (state s) (inputs i) = Zmod.unsigned (N.v41238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41238 s i)) at 1.
  unfold R.v41238, N.v41238.
  rewrite ?node_8745.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41239 (s : N.State) (i : N.Inputs) :
  R.v41239 (state s) (inputs i) = Zmod.unsigned (N.v41239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41239 s i)) at 1.
  unfold R.v41239, N.v41239.
  rewrite ?node_8741.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41240 (s : N.State) (i : N.Inputs) :
  R.v41240 (state s) (inputs i) = Zmod.unsigned (N.v41240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41240 s i)) at 1.
  unfold R.v41240, N.v41240.
  rewrite ?node_8737.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41241 (s : N.State) (i : N.Inputs) :
  R.v41241 (state s) (inputs i) = Zmod.unsigned (N.v41241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41241 s i)) at 1.
  unfold R.v41241, N.v41241.
  unfold R.v6, N.v6.
  rewrite ?node_8729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41242 (s : N.State) (i : N.Inputs) :
  R.v41242 (state s) (inputs i) = Zmod.unsigned (N.v41242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41242 s i)) at 1.
  unfold R.v41242, N.v41242.
  unfold R.v6, N.v6.
  rewrite ?node_8722.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41243 (s : N.State) (i : N.Inputs) :
  R.v41243 (state s) (inputs i) = Zmod.unsigned (N.v41243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41243 s i)) at 1.
  unfold R.v41243, N.v41243.
  rewrite ?node_41241.
  rewrite ?node_41242.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41244 (s : N.State) (i : N.Inputs) :
  R.v41244 (state s) (inputs i) = Zmod.unsigned (N.v41244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41244 s i)) at 1.
  unfold R.v41244, N.v41244.
  unfold R.v16484, N.v16484.
  rewrite ?node_41243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41245 (s : N.State) (i : N.Inputs) :
  R.v41245 (state s) (inputs i) = Zmod.unsigned (N.v41245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41245 s i)) at 1.
  unfold R.v41245, N.v41245.
  rewrite ?node_41238.
  rewrite ?node_41239.
  rewrite ?node_41240.
  rewrite ?node_41244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41246 (s : N.State) (i : N.Inputs) :
  R.v41246 (state s) (inputs i) = Zmod.unsigned (N.v41246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41246 s i)) at 1.
  unfold R.v41246, N.v41246.
  unfold R.v6, N.v6.
  rewrite ?node_41245.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41247 (s : N.State) (i : N.Inputs) :
  R.v41247 (state s) (inputs i) = Zmod.unsigned (N.v41247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41247 s i)) at 1.
  unfold R.v41247, N.v41247.
  rewrite ?node_8746.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41248 (s : N.State) (i : N.Inputs) :
  R.v41248 (state s) (inputs i) = Zmod.unsigned (N.v41248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41248 s i)) at 1.
  unfold R.v41248, N.v41248.
  unfold R.v6, N.v6.
  rewrite ?node_8876.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41249 (s : N.State) (i : N.Inputs) :
  R.v41249 (state s) (inputs i) = Zmod.unsigned (N.v41249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41249 s i)) at 1.
  unfold R.v41249, N.v41249.
  unfold R.v6, N.v6.
  rewrite ?node_8920.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41250 (s : N.State) (i : N.Inputs) :
  R.v41250 (state s) (inputs i) = Zmod.unsigned (N.v41250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41250 s i)) at 1.
  unfold R.v41250, N.v41250.
  rewrite ?node_41247.
  rewrite ?node_41248.
  rewrite ?node_41249.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41251 (s : N.State) (i : N.Inputs) :
  R.v41251 (state s) (inputs i) = Zmod.unsigned (N.v41251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41251 s i)) at 1.
  unfold R.v41251, N.v41251.
  rewrite ?node_41246.
  rewrite ?node_41250.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41252 (s : N.State) (i : N.Inputs) :
  R.v41252 (state s) (inputs i) = Zmod.unsigned (N.v41252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41252 s i)) at 1.
  unfold R.v41252, N.v41252.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41253 (s : N.State) (i : N.Inputs) :
  R.v41253 (state s) (inputs i) = Zmod.unsigned (N.v41253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41253 s i)) at 1.
  unfold R.v41253, N.v41253.
  rewrite ?node_8737.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41254 (s : N.State) (i : N.Inputs) :
  R.v41254 (state s) (inputs i) = Zmod.unsigned (N.v41254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41254 s i)) at 1.
  unfold R.v41254, N.v41254.
  unfold R.v6, N.v6.
  rewrite ?node_8729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41255 (s : N.State) (i : N.Inputs) :
  R.v41255 (state s) (inputs i) = Zmod.unsigned (N.v41255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41255 s i)) at 1.
  unfold R.v41255, N.v41255.
  unfold R.v6, N.v6.
  rewrite ?node_8722.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41256 (s : N.State) (i : N.Inputs) :
  R.v41256 (state s) (inputs i) = Zmod.unsigned (N.v41256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41256 s i)) at 1.
  unfold R.v41256, N.v41256.
  rewrite ?node_41254.
  rewrite ?node_41255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41257 (s : N.State) (i : N.Inputs) :
  R.v41257 (state s) (inputs i) = Zmod.unsigned (N.v41257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41257 s i)) at 1.
  unfold R.v41257, N.v41257.
  unfold R.v16484, N.v16484.
  rewrite ?node_41256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41258 (s : N.State) (i : N.Inputs) :
  R.v41258 (state s) (inputs i) = Zmod.unsigned (N.v41258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41258 s i)) at 1.
  unfold R.v41258, N.v41258.
  rewrite ?node_41253.
  rewrite ?node_41257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41259 (s : N.State) (i : N.Inputs) :
  R.v41259 (state s) (inputs i) = Zmod.unsigned (N.v41259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41259 s i)) at 1.
  unfold R.v41259, N.v41259.
  unfold R.v6, N.v6.
  rewrite ?node_41258.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41260 (s : N.State) (i : N.Inputs) :
  R.v41260 (state s) (inputs i) = Zmod.unsigned (N.v41260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41260 s i)) at 1.
  unfold R.v41260, N.v41260.
  rewrite ?node_8738.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41261 (s : N.State) (i : N.Inputs) :
  R.v41261 (state s) (inputs i) = Zmod.unsigned (N.v41261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41261 s i)) at 1.
  unfold R.v41261, N.v41261.
  unfold R.v6, N.v6.
  rewrite ?node_8876.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41262 (s : N.State) (i : N.Inputs) :
  R.v41262 (state s) (inputs i) = Zmod.unsigned (N.v41262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41262 s i)) at 1.
  unfold R.v41262, N.v41262.
  rewrite ?node_41260.
  rewrite ?node_41261.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41263 (s : N.State) (i : N.Inputs) :
  R.v41263 (state s) (inputs i) = Zmod.unsigned (N.v41263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41263 s i)) at 1.
  unfold R.v41263, N.v41263.
  rewrite ?node_41259.
  rewrite ?node_41262.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41264 (s : N.State) (i : N.Inputs) :
  R.v41264 (state s) (inputs i) = Zmod.unsigned (N.v41264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41264 s i)) at 1.
  unfold R.v41264, N.v41264.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41265 (s : N.State) (i : N.Inputs) :
  R.v41265 (state s) (inputs i) = Zmod.unsigned (N.v41265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41265 s i)) at 1.
  unfold R.v41265, N.v41265.
  rewrite ?node_8745.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41266 (s : N.State) (i : N.Inputs) :
  R.v41266 (state s) (inputs i) = Zmod.unsigned (N.v41266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41266 s i)) at 1.
  unfold R.v41266, N.v41266.
  unfold R.v6, N.v6.
  rewrite ?node_8741.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41267 (s : N.State) (i : N.Inputs) :
  R.v41267 (state s) (inputs i) = Zmod.unsigned (N.v41267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41267 s i)) at 1.
  unfold R.v41267, N.v41267.
  unfold R.v6, N.v6.
  rewrite ?node_8738.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41268 (s : N.State) (i : N.Inputs) :
  R.v41268 (state s) (inputs i) = Zmod.unsigned (N.v41268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41268 s i)) at 1.
  unfold R.v41268, N.v41268.
  rewrite ?node_41266.
  rewrite ?node_41267.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41269 (s : N.State) (i : N.Inputs) :
  R.v41269 (state s) (inputs i) = Zmod.unsigned (N.v41269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41269 s i)) at 1.
  unfold R.v41269, N.v41269.
  unfold R.v16484, N.v16484.
  rewrite ?node_41268.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41270 (s : N.State) (i : N.Inputs) :
  R.v41270 (state s) (inputs i) = Zmod.unsigned (N.v41270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41270 s i)) at 1.
  unfold R.v41270, N.v41270.
  rewrite ?node_41265.
  rewrite ?node_41269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41271 (s : N.State) (i : N.Inputs) :
  R.v41271 (state s) (inputs i) = Zmod.unsigned (N.v41271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41271 s i)) at 1.
  unfold R.v41271, N.v41271.
  unfold R.v6, N.v6.
  rewrite ?node_41270.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41272 (s : N.State) (i : N.Inputs) :
  R.v41272 (state s) (inputs i) = Zmod.unsigned (N.v41272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41272 s i)) at 1.
  unfold R.v41272, N.v41272.
  rewrite ?node_8746.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41273 (s : N.State) (i : N.Inputs) :
  R.v41273 (state s) (inputs i) = Zmod.unsigned (N.v41273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41273 s i)) at 1.
  unfold R.v41273, N.v41273.
  unfold R.v6, N.v6.
  rewrite ?node_8920.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41274 (s : N.State) (i : N.Inputs) :
  R.v41274 (state s) (inputs i) = Zmod.unsigned (N.v41274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41274 s i)) at 1.
  unfold R.v41274, N.v41274.
  rewrite ?node_41272.
  rewrite ?node_41273.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41275 (s : N.State) (i : N.Inputs) :
  R.v41275 (state s) (inputs i) = Zmod.unsigned (N.v41275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41275 s i)) at 1.
  unfold R.v41275, N.v41275.
  rewrite ?node_41271.
  rewrite ?node_41274.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41276 (s : N.State) (i : N.Inputs) :
  R.v41276 (state s) (inputs i) = Zmod.unsigned (N.v41276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41276 s i)) at 1.
  unfold R.v41276, N.v41276.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41277 (s : N.State) (i : N.Inputs) :
  R.v41277 (state s) (inputs i) = Zmod.unsigned (N.v41277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41277 s i)) at 1.
  unfold R.v41277, N.v41277.
  rewrite ?node_8765.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41278 (s : N.State) (i : N.Inputs) :
  R.v41278 (state s) (inputs i) = Zmod.unsigned (N.v41278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41278 s i)) at 1.
  unfold R.v41278, N.v41278.
  rewrite ?node_8761.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41279 (s : N.State) (i : N.Inputs) :
  R.v41279 (state s) (inputs i) = Zmod.unsigned (N.v41279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41279 s i)) at 1.
  unfold R.v41279, N.v41279.
  rewrite ?node_8757.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41280 (s : N.State) (i : N.Inputs) :
  R.v41280 (state s) (inputs i) = Zmod.unsigned (N.v41280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41280 s i)) at 1.
  unfold R.v41280, N.v41280.
  unfold R.v6, N.v6.
  rewrite ?node_8753.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41281 (s : N.State) (i : N.Inputs) :
  R.v41281 (state s) (inputs i) = Zmod.unsigned (N.v41281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41281 s i)) at 1.
  unfold R.v41281, N.v41281.
  unfold R.v6, N.v6.
  rewrite ?node_8750.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41282 (s : N.State) (i : N.Inputs) :
  R.v41282 (state s) (inputs i) = Zmod.unsigned (N.v41282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41282 s i)) at 1.
  unfold R.v41282, N.v41282.
  rewrite ?node_41280.
  rewrite ?node_41281.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41283 (s : N.State) (i : N.Inputs) :
  R.v41283 (state s) (inputs i) = Zmod.unsigned (N.v41283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41283 s i)) at 1.
  unfold R.v41283, N.v41283.
  unfold R.v16484, N.v16484.
  rewrite ?node_41282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41284 (s : N.State) (i : N.Inputs) :
  R.v41284 (state s) (inputs i) = Zmod.unsigned (N.v41284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41284 s i)) at 1.
  unfold R.v41284, N.v41284.
  rewrite ?node_41277.
  rewrite ?node_41278.
  rewrite ?node_41279.
  rewrite ?node_41283.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41285 (s : N.State) (i : N.Inputs) :
  R.v41285 (state s) (inputs i) = Zmod.unsigned (N.v41285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41285 s i)) at 1.
  unfold R.v41285, N.v41285.
  unfold R.v6, N.v6.
  rewrite ?node_41284.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41286 (s : N.State) (i : N.Inputs) :
  R.v41286 (state s) (inputs i) = Zmod.unsigned (N.v41286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41286 s i)) at 1.
  unfold R.v41286, N.v41286.
  rewrite ?node_8766.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41287 (s : N.State) (i : N.Inputs) :
  R.v41287 (state s) (inputs i) = Zmod.unsigned (N.v41287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41287 s i)) at 1.
  unfold R.v41287, N.v41287.
  unfold R.v6, N.v6.
  rewrite ?node_8896.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41288 (s : N.State) (i : N.Inputs) :
  R.v41288 (state s) (inputs i) = Zmod.unsigned (N.v41288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41288 s i)) at 1.
  unfold R.v41288, N.v41288.
  unfold R.v6, N.v6.
  rewrite ?node_8924.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41289 (s : N.State) (i : N.Inputs) :
  R.v41289 (state s) (inputs i) = Zmod.unsigned (N.v41289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41289 s i)) at 1.
  unfold R.v41289, N.v41289.
  rewrite ?node_41286.
  rewrite ?node_41287.
  rewrite ?node_41288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41290 (s : N.State) (i : N.Inputs) :
  R.v41290 (state s) (inputs i) = Zmod.unsigned (N.v41290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41290 s i)) at 1.
  unfold R.v41290, N.v41290.
  rewrite ?node_41285.
  rewrite ?node_41289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41291 (s : N.State) (i : N.Inputs) :
  R.v41291 (state s) (inputs i) = Zmod.unsigned (N.v41291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41291 s i)) at 1.
  unfold R.v41291, N.v41291.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41292 (s : N.State) (i : N.Inputs) :
  R.v41292 (state s) (inputs i) = Zmod.unsigned (N.v41292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41292 s i)) at 1.
  unfold R.v41292, N.v41292.
  rewrite ?node_8757.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41293 (s : N.State) (i : N.Inputs) :
  R.v41293 (state s) (inputs i) = Zmod.unsigned (N.v41293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41293 s i)) at 1.
  unfold R.v41293, N.v41293.
  unfold R.v6, N.v6.
  rewrite ?node_8753.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41294 (s : N.State) (i : N.Inputs) :
  R.v41294 (state s) (inputs i) = Zmod.unsigned (N.v41294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41294 s i)) at 1.
  unfold R.v41294, N.v41294.
  unfold R.v6, N.v6.
  rewrite ?node_8750.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41295 (s : N.State) (i : N.Inputs) :
  R.v41295 (state s) (inputs i) = Zmod.unsigned (N.v41295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41295 s i)) at 1.
  unfold R.v41295, N.v41295.
  rewrite ?node_41293.
  rewrite ?node_41294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41296 (s : N.State) (i : N.Inputs) :
  R.v41296 (state s) (inputs i) = Zmod.unsigned (N.v41296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41296 s i)) at 1.
  unfold R.v41296, N.v41296.
  unfold R.v16484, N.v16484.
  rewrite ?node_41295.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41297 (s : N.State) (i : N.Inputs) :
  R.v41297 (state s) (inputs i) = Zmod.unsigned (N.v41297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41297 s i)) at 1.
  unfold R.v41297, N.v41297.
  rewrite ?node_41292.
  rewrite ?node_41296.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41298 (s : N.State) (i : N.Inputs) :
  R.v41298 (state s) (inputs i) = Zmod.unsigned (N.v41298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41298 s i)) at 1.
  unfold R.v41298, N.v41298.
  unfold R.v6, N.v6.
  rewrite ?node_41297.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41299 (s : N.State) (i : N.Inputs) :
  R.v41299 (state s) (inputs i) = Zmod.unsigned (N.v41299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41299 s i)) at 1.
  unfold R.v41299, N.v41299.
  rewrite ?node_8758.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41300 (s : N.State) (i : N.Inputs) :
  R.v41300 (state s) (inputs i) = Zmod.unsigned (N.v41300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41300 s i)) at 1.
  unfold R.v41300, N.v41300.
  unfold R.v6, N.v6.
  rewrite ?node_8896.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41301 (s : N.State) (i : N.Inputs) :
  R.v41301 (state s) (inputs i) = Zmod.unsigned (N.v41301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41301 s i)) at 1.
  unfold R.v41301, N.v41301.
  rewrite ?node_41299.
  rewrite ?node_41300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41302 (s : N.State) (i : N.Inputs) :
  R.v41302 (state s) (inputs i) = Zmod.unsigned (N.v41302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41302 s i)) at 1.
  unfold R.v41302, N.v41302.
  rewrite ?node_41298.
  rewrite ?node_41301.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41303 (s : N.State) (i : N.Inputs) :
  R.v41303 (state s) (inputs i) = Zmod.unsigned (N.v41303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41303 s i)) at 1.
  unfold R.v41303, N.v41303.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41304 (s : N.State) (i : N.Inputs) :
  R.v41304 (state s) (inputs i) = Zmod.unsigned (N.v41304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41304 s i)) at 1.
  unfold R.v41304, N.v41304.
  rewrite ?node_8765.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41305 (s : N.State) (i : N.Inputs) :
  R.v41305 (state s) (inputs i) = Zmod.unsigned (N.v41305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41305 s i)) at 1.
  unfold R.v41305, N.v41305.
  unfold R.v6, N.v6.
  rewrite ?node_8761.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41306 (s : N.State) (i : N.Inputs) :
  R.v41306 (state s) (inputs i) = Zmod.unsigned (N.v41306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41306 s i)) at 1.
  unfold R.v41306, N.v41306.
  unfold R.v6, N.v6.
  rewrite ?node_8758.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41307 (s : N.State) (i : N.Inputs) :
  R.v41307 (state s) (inputs i) = Zmod.unsigned (N.v41307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41307 s i)) at 1.
  unfold R.v41307, N.v41307.
  rewrite ?node_41305.
  rewrite ?node_41306.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41308 (s : N.State) (i : N.Inputs) :
  R.v41308 (state s) (inputs i) = Zmod.unsigned (N.v41308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41308 s i)) at 1.
  unfold R.v41308, N.v41308.
  unfold R.v16484, N.v16484.
  rewrite ?node_41307.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41309 (s : N.State) (i : N.Inputs) :
  R.v41309 (state s) (inputs i) = Zmod.unsigned (N.v41309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41309 s i)) at 1.
  unfold R.v41309, N.v41309.
  rewrite ?node_41304.
  rewrite ?node_41308.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41310 (s : N.State) (i : N.Inputs) :
  R.v41310 (state s) (inputs i) = Zmod.unsigned (N.v41310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41310 s i)) at 1.
  unfold R.v41310, N.v41310.
  unfold R.v6, N.v6.
  rewrite ?node_41309.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41311 (s : N.State) (i : N.Inputs) :
  R.v41311 (state s) (inputs i) = Zmod.unsigned (N.v41311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41311 s i)) at 1.
  unfold R.v41311, N.v41311.
  rewrite ?node_8766.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41312 (s : N.State) (i : N.Inputs) :
  R.v41312 (state s) (inputs i) = Zmod.unsigned (N.v41312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41312 s i)) at 1.
  unfold R.v41312, N.v41312.
  unfold R.v6, N.v6.
  rewrite ?node_8924.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41313 (s : N.State) (i : N.Inputs) :
  R.v41313 (state s) (inputs i) = Zmod.unsigned (N.v41313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41313 s i)) at 1.
  unfold R.v41313, N.v41313.
  rewrite ?node_41311.
  rewrite ?node_41312.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41314 (s : N.State) (i : N.Inputs) :
  R.v41314 (state s) (inputs i) = Zmod.unsigned (N.v41314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41314 s i)) at 1.
  unfold R.v41314, N.v41314.
  rewrite ?node_41310.
  rewrite ?node_41313.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41315 (s : N.State) (i : N.Inputs) :
  R.v41315 (state s) (inputs i) = Zmod.unsigned (N.v41315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41315 s i)) at 1.
  unfold R.v41315, N.v41315.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41316 (s : N.State) (i : N.Inputs) :
  R.v41316 (state s) (inputs i) = Zmod.unsigned (N.v41316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41316 s i)) at 1.
  unfold R.v41316, N.v41316.
  unfold R.v6, N.v6.
  rewrite ?node_8771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41317 (s : N.State) (i : N.Inputs) :
  R.v41317 (state s) (inputs i) = Zmod.unsigned (N.v41317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41317 s i)) at 1.
  unfold R.v41317, N.v41317.
  unfold R.v6, N.v6.
  rewrite ?node_8770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41318 (s : N.State) (i : N.Inputs) :
  R.v41318 (state s) (inputs i) = Zmod.unsigned (N.v41318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41318 s i)) at 1.
  unfold R.v41318, N.v41318.
  rewrite ?node_41316.
  rewrite ?node_41317.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41319 (s : N.State) (i : N.Inputs) :
  R.v41319 (state s) (inputs i) = Zmod.unsigned (N.v41319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41319 s i)) at 1.
  unfold R.v41319, N.v41319.
  unfold R.v16463, N.v16463.
  rewrite ?node_41318.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41320 (s : N.State) (i : N.Inputs) :
  R.v41320 (state s) (inputs i) = Zmod.unsigned (N.v41320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41320 s i)) at 1.
  unfold R.v41320, N.v41320.
  rewrite ?node_8772.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41321 (s : N.State) (i : N.Inputs) :
  R.v41321 (state s) (inputs i) = Zmod.unsigned (N.v41321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41321 s i)) at 1.
  unfold R.v41321, N.v41321.
  unfold R.v6, N.v6.
  rewrite ?node_8926.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41322 (s : N.State) (i : N.Inputs) :
  R.v41322 (state s) (inputs i) = Zmod.unsigned (N.v41322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41322 s i)) at 1.
  unfold R.v41322, N.v41322.
  rewrite ?node_41320.
  rewrite ?node_41321.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41323 (s : N.State) (i : N.Inputs) :
  R.v41323 (state s) (inputs i) = Zmod.unsigned (N.v41323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41323 s i)) at 1.
  unfold R.v41323, N.v41323.
  rewrite ?node_41319.
  rewrite ?node_41322.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41324 (s : N.State) (i : N.Inputs) :
  R.v41324 (state s) (inputs i) = Zmod.unsigned (N.v41324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41324 s i)) at 1.
  unfold R.v41324, N.v41324.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41325 (s : N.State) (i : N.Inputs) :
  R.v41325 (state s) (inputs i) = Zmod.unsigned (N.v41325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41325 s i)) at 1.
  unfold R.v41325, N.v41325.
  rewrite ?node_8848.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41326 (s : N.State) (i : N.Inputs) :
  R.v41326 (state s) (inputs i) = Zmod.unsigned (N.v41326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41326 s i)) at 1.
  unfold R.v41326, N.v41326.
  rewrite ?node_8844.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41327 (s : N.State) (i : N.Inputs) :
  R.v41327 (state s) (inputs i) = Zmod.unsigned (N.v41327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41327 s i)) at 1.
  unfold R.v41327, N.v41327.
  rewrite ?node_8836.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41328 (s : N.State) (i : N.Inputs) :
  R.v41328 (state s) (inputs i) = Zmod.unsigned (N.v41328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41328 s i)) at 1.
  unfold R.v41328, N.v41328.
  unfold R.v6, N.v6.
  rewrite ?node_8828.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41329 (s : N.State) (i : N.Inputs) :
  R.v41329 (state s) (inputs i) = Zmod.unsigned (N.v41329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41329 s i)) at 1.
  unfold R.v41329, N.v41329.
  unfold R.v6, N.v6.
  rewrite ?node_8821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41330 (s : N.State) (i : N.Inputs) :
  R.v41330 (state s) (inputs i) = Zmod.unsigned (N.v41330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41330 s i)) at 1.
  unfold R.v41330, N.v41330.
  rewrite ?node_41328.
  rewrite ?node_41329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41331 (s : N.State) (i : N.Inputs) :
  R.v41331 (state s) (inputs i) = Zmod.unsigned (N.v41331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41331 s i)) at 1.
  unfold R.v41331, N.v41331.
  unfold R.v16484, N.v16484.
  rewrite ?node_41330.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41332 (s : N.State) (i : N.Inputs) :
  R.v41332 (state s) (inputs i) = Zmod.unsigned (N.v41332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41332 s i)) at 1.
  unfold R.v41332, N.v41332.
  rewrite ?node_41325.
  rewrite ?node_41326.
  rewrite ?node_41327.
  rewrite ?node_41331.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41333 (s : N.State) (i : N.Inputs) :
  R.v41333 (state s) (inputs i) = Zmod.unsigned (N.v41333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41333 s i)) at 1.
  unfold R.v41333, N.v41333.
  unfold R.v6, N.v6.
  rewrite ?node_41332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41334 (s : N.State) (i : N.Inputs) :
  R.v41334 (state s) (inputs i) = Zmod.unsigned (N.v41334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41334 s i)) at 1.
  unfold R.v41334, N.v41334.
  rewrite ?node_8849.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41335 (s : N.State) (i : N.Inputs) :
  R.v41335 (state s) (inputs i) = Zmod.unsigned (N.v41335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41335 s i)) at 1.
  unfold R.v41335, N.v41335.
  unfold R.v6, N.v6.
  rewrite ?node_8985.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41336 (s : N.State) (i : N.Inputs) :
  R.v41336 (state s) (inputs i) = Zmod.unsigned (N.v41336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41336 s i)) at 1.
  unfold R.v41336, N.v41336.
  unfold R.v6, N.v6.
  rewrite ?node_9054.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41337 (s : N.State) (i : N.Inputs) :
  R.v41337 (state s) (inputs i) = Zmod.unsigned (N.v41337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41337 s i)) at 1.
  unfold R.v41337, N.v41337.
  rewrite ?node_41334.
  rewrite ?node_41335.
  rewrite ?node_41336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41338 (s : N.State) (i : N.Inputs) :
  R.v41338 (state s) (inputs i) = Zmod.unsigned (N.v41338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41338 s i)) at 1.
  unfold R.v41338, N.v41338.
  rewrite ?node_41333.
  rewrite ?node_41337.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41339 (s : N.State) (i : N.Inputs) :
  R.v41339 (state s) (inputs i) = Zmod.unsigned (N.v41339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41339 s i)) at 1.
  unfold R.v41339, N.v41339.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41340 (s : N.State) (i : N.Inputs) :
  R.v41340 (state s) (inputs i) = Zmod.unsigned (N.v41340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41340 s i)) at 1.
  unfold R.v41340, N.v41340.
  rewrite ?node_8836.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41341 (s : N.State) (i : N.Inputs) :
  R.v41341 (state s) (inputs i) = Zmod.unsigned (N.v41341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41341 s i)) at 1.
  unfold R.v41341, N.v41341.
  unfold R.v6, N.v6.
  rewrite ?node_8828.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41342 (s : N.State) (i : N.Inputs) :
  R.v41342 (state s) (inputs i) = Zmod.unsigned (N.v41342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41342 s i)) at 1.
  unfold R.v41342, N.v41342.
  unfold R.v6, N.v6.
  rewrite ?node_8821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41343 (s : N.State) (i : N.Inputs) :
  R.v41343 (state s) (inputs i) = Zmod.unsigned (N.v41343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41343 s i)) at 1.
  unfold R.v41343, N.v41343.
  rewrite ?node_41341.
  rewrite ?node_41342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41344 (s : N.State) (i : N.Inputs) :
  R.v41344 (state s) (inputs i) = Zmod.unsigned (N.v41344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41344 s i)) at 1.
  unfold R.v41344, N.v41344.
  unfold R.v16484, N.v16484.
  rewrite ?node_41343.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41345 (s : N.State) (i : N.Inputs) :
  R.v41345 (state s) (inputs i) = Zmod.unsigned (N.v41345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41345 s i)) at 1.
  unfold R.v41345, N.v41345.
  rewrite ?node_41340.
  rewrite ?node_41344.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41346 (s : N.State) (i : N.Inputs) :
  R.v41346 (state s) (inputs i) = Zmod.unsigned (N.v41346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41346 s i)) at 1.
  unfold R.v41346, N.v41346.
  unfold R.v6, N.v6.
  rewrite ?node_41345.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41347 (s : N.State) (i : N.Inputs) :
  R.v41347 (state s) (inputs i) = Zmod.unsigned (N.v41347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41347 s i)) at 1.
  unfold R.v41347, N.v41347.
  rewrite ?node_8837.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41348 (s : N.State) (i : N.Inputs) :
  R.v41348 (state s) (inputs i) = Zmod.unsigned (N.v41348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41348 s i)) at 1.
  unfold R.v41348, N.v41348.
  unfold R.v6, N.v6.
  rewrite ?node_8985.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41349 (s : N.State) (i : N.Inputs) :
  R.v41349 (state s) (inputs i) = Zmod.unsigned (N.v41349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41349 s i)) at 1.
  unfold R.v41349, N.v41349.
  rewrite ?node_41347.
  rewrite ?node_41348.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41350 (s : N.State) (i : N.Inputs) :
  R.v41350 (state s) (inputs i) = Zmod.unsigned (N.v41350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41350 s i)) at 1.
  unfold R.v41350, N.v41350.
  rewrite ?node_41346.
  rewrite ?node_41349.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41351 (s : N.State) (i : N.Inputs) :
  R.v41351 (state s) (inputs i) = Zmod.unsigned (N.v41351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41351 s i)) at 1.
  unfold R.v41351, N.v41351.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41352 (s : N.State) (i : N.Inputs) :
  R.v41352 (state s) (inputs i) = Zmod.unsigned (N.v41352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41352 s i)) at 1.
  unfold R.v41352, N.v41352.
  rewrite ?node_8848.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41353 (s : N.State) (i : N.Inputs) :
  R.v41353 (state s) (inputs i) = Zmod.unsigned (N.v41353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41353 s i)) at 1.
  unfold R.v41353, N.v41353.
  unfold R.v6, N.v6.
  rewrite ?node_8844.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41354 (s : N.State) (i : N.Inputs) :
  R.v41354 (state s) (inputs i) = Zmod.unsigned (N.v41354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41354 s i)) at 1.
  unfold R.v41354, N.v41354.
  unfold R.v6, N.v6.
  rewrite ?node_8837.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41355 (s : N.State) (i : N.Inputs) :
  R.v41355 (state s) (inputs i) = Zmod.unsigned (N.v41355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41355 s i)) at 1.
  unfold R.v41355, N.v41355.
  rewrite ?node_41353.
  rewrite ?node_41354.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41356 (s : N.State) (i : N.Inputs) :
  R.v41356 (state s) (inputs i) = Zmod.unsigned (N.v41356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41356 s i)) at 1.
  unfold R.v41356, N.v41356.
  unfold R.v16484, N.v16484.
  rewrite ?node_41355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41357 (s : N.State) (i : N.Inputs) :
  R.v41357 (state s) (inputs i) = Zmod.unsigned (N.v41357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41357 s i)) at 1.
  unfold R.v41357, N.v41357.
  rewrite ?node_41352.
  rewrite ?node_41356.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41358 (s : N.State) (i : N.Inputs) :
  R.v41358 (state s) (inputs i) = Zmod.unsigned (N.v41358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41358 s i)) at 1.
  unfold R.v41358, N.v41358.
  unfold R.v6, N.v6.
  rewrite ?node_41357.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41359 (s : N.State) (i : N.Inputs) :
  R.v41359 (state s) (inputs i) = Zmod.unsigned (N.v41359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41359 s i)) at 1.
  unfold R.v41359, N.v41359.
  rewrite ?node_8849.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41360 (s : N.State) (i : N.Inputs) :
  R.v41360 (state s) (inputs i) = Zmod.unsigned (N.v41360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41360 s i)) at 1.
  unfold R.v41360, N.v41360.
  unfold R.v6, N.v6.
  rewrite ?node_9054.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41361 (s : N.State) (i : N.Inputs) :
  R.v41361 (state s) (inputs i) = Zmod.unsigned (N.v41361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41361 s i)) at 1.
  unfold R.v41361, N.v41361.
  rewrite ?node_41359.
  rewrite ?node_41360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41362 (s : N.State) (i : N.Inputs) :
  R.v41362 (state s) (inputs i) = Zmod.unsigned (N.v41362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41362 s i)) at 1.
  unfold R.v41362, N.v41362.
  rewrite ?node_41358.
  rewrite ?node_41361.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41363 (s : N.State) (i : N.Inputs) :
  R.v41363 (state s) (inputs i) = Zmod.unsigned (N.v41363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41363 s i)) at 1.
  unfold R.v41363, N.v41363.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41364 (s : N.State) (i : N.Inputs) :
  R.v41364 (state s) (inputs i) = Zmod.unsigned (N.v41364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41364 s i)) at 1.
  unfold R.v41364, N.v41364.
  rewrite ?node_8876.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41365 (s : N.State) (i : N.Inputs) :
  R.v41365 (state s) (inputs i) = Zmod.unsigned (N.v41365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41365 s i)) at 1.
  unfold R.v41365, N.v41365.
  unfold R.v16463, N.v16463.
  rewrite !state_r838_nr_5F838.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r838_nr_5F838 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41366 (s : N.State) (i : N.Inputs) :
  R.v41366 (state s) (inputs i) = Zmod.unsigned (N.v41366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41366 s i)) at 1.
  unfold R.v41366, N.v41366.
  rewrite ?node_8871.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41367 (s : N.State) (i : N.Inputs) :
  R.v41367 (state s) (inputs i) = Zmod.unsigned (N.v41367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41367 s i)) at 1.
  unfold R.v41367, N.v41367.
  unfold R.v6, N.v6.
  rewrite ?node_8863.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41368 (s : N.State) (i : N.Inputs) :
  R.v41368 (state s) (inputs i) = Zmod.unsigned (N.v41368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41368 s i)) at 1.
  unfold R.v41368, N.v41368.
  unfold R.v6, N.v6.
  rewrite ?node_8856.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41369 (s : N.State) (i : N.Inputs) :
  R.v41369 (state s) (inputs i) = Zmod.unsigned (N.v41369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41369 s i)) at 1.
  unfold R.v41369, N.v41369.
  rewrite ?node_41367.
  rewrite ?node_41368.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41370 (s : N.State) (i : N.Inputs) :
  R.v41370 (state s) (inputs i) = Zmod.unsigned (N.v41370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41370 s i)) at 1.
  unfold R.v41370, N.v41370.
  unfold R.v16484, N.v16484.
  rewrite ?node_41369.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41371 (s : N.State) (i : N.Inputs) :
  R.v41371 (state s) (inputs i) = Zmod.unsigned (N.v41371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41371 s i)) at 1.
  unfold R.v41371, N.v41371.
  rewrite ?node_41364.
  rewrite ?node_41365.
  rewrite ?node_41366.
  rewrite ?node_41370.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41372 (s : N.State) (i : N.Inputs) :
  R.v41372 (state s) (inputs i) = Zmod.unsigned (N.v41372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41372 s i)) at 1.
  unfold R.v41372, N.v41372.
  unfold R.v6, N.v6.
  rewrite ?node_41371.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41373 (s : N.State) (i : N.Inputs) :
  R.v41373 (state s) (inputs i) = Zmod.unsigned (N.v41373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41373 s i)) at 1.
  unfold R.v41373, N.v41373.
  rewrite ?node_8877.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41374 (s : N.State) (i : N.Inputs) :
  R.v41374 (state s) (inputs i) = Zmod.unsigned (N.v41374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41374 s i)) at 1.
  unfold R.v41374, N.v41374.
  unfold R.v6, N.v6.
  rewrite ?node_9013.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41375 (s : N.State) (i : N.Inputs) :
  R.v41375 (state s) (inputs i) = Zmod.unsigned (N.v41375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41375 s i)) at 1.
  unfold R.v41375, N.v41375.
  unfold R.v6, N.v6.
  rewrite ?node_9057.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41376 (s : N.State) (i : N.Inputs) :
  R.v41376 (state s) (inputs i) = Zmod.unsigned (N.v41376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41376 s i)) at 1.
  unfold R.v41376, N.v41376.
  rewrite ?node_41373.
  rewrite ?node_41374.
  rewrite ?node_41375.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41377 (s : N.State) (i : N.Inputs) :
  R.v41377 (state s) (inputs i) = Zmod.unsigned (N.v41377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41377 s i)) at 1.
  unfold R.v41377, N.v41377.
  rewrite ?node_41372.
  rewrite ?node_41376.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41378 (s : N.State) (i : N.Inputs) :
  R.v41378 (state s) (inputs i) = Zmod.unsigned (N.v41378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41378 s i)) at 1.
  unfold R.v41378, N.v41378.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41379 (s : N.State) (i : N.Inputs) :
  R.v41379 (state s) (inputs i) = Zmod.unsigned (N.v41379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41379 s i)) at 1.
  unfold R.v41379, N.v41379.
  rewrite ?node_8871.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41380 (s : N.State) (i : N.Inputs) :
  R.v41380 (state s) (inputs i) = Zmod.unsigned (N.v41380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41380 s i)) at 1.
  unfold R.v41380, N.v41380.
  unfold R.v6, N.v6.
  rewrite ?node_8863.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41381 (s : N.State) (i : N.Inputs) :
  R.v41381 (state s) (inputs i) = Zmod.unsigned (N.v41381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41381 s i)) at 1.
  unfold R.v41381, N.v41381.
  unfold R.v6, N.v6.
  rewrite ?node_8856.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41382 (s : N.State) (i : N.Inputs) :
  R.v41382 (state s) (inputs i) = Zmod.unsigned (N.v41382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41382 s i)) at 1.
  unfold R.v41382, N.v41382.
  rewrite ?node_41380.
  rewrite ?node_41381.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41383 (s : N.State) (i : N.Inputs) :
  R.v41383 (state s) (inputs i) = Zmod.unsigned (N.v41383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41383 s i)) at 1.
  unfold R.v41383, N.v41383.
  unfold R.v16484, N.v16484.
  rewrite ?node_41382.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41384 (s : N.State) (i : N.Inputs) :
  R.v41384 (state s) (inputs i) = Zmod.unsigned (N.v41384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41384 s i)) at 1.
  unfold R.v41384, N.v41384.
  rewrite ?node_41379.
  rewrite ?node_41383.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41385 (s : N.State) (i : N.Inputs) :
  R.v41385 (state s) (inputs i) = Zmod.unsigned (N.v41385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41385 s i)) at 1.
  unfold R.v41385, N.v41385.
  unfold R.v6, N.v6.
  rewrite ?node_41384.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41386 (s : N.State) (i : N.Inputs) :
  R.v41386 (state s) (inputs i) = Zmod.unsigned (N.v41386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41386 s i)) at 1.
  unfold R.v41386, N.v41386.
  rewrite ?node_8872.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41387 (s : N.State) (i : N.Inputs) :
  R.v41387 (state s) (inputs i) = Zmod.unsigned (N.v41387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41387 s i)) at 1.
  unfold R.v41387, N.v41387.
  unfold R.v6, N.v6.
  rewrite ?node_9013.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41388 (s : N.State) (i : N.Inputs) :
  R.v41388 (state s) (inputs i) = Zmod.unsigned (N.v41388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41388 s i)) at 1.
  unfold R.v41388, N.v41388.
  rewrite ?node_41386.
  rewrite ?node_41387.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41389 (s : N.State) (i : N.Inputs) :
  R.v41389 (state s) (inputs i) = Zmod.unsigned (N.v41389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41389 s i)) at 1.
  unfold R.v41389, N.v41389.
  rewrite ?node_41385.
  rewrite ?node_41388.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41390 (s : N.State) (i : N.Inputs) :
  R.v41390 (state s) (inputs i) = Zmod.unsigned (N.v41390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41390 s i)) at 1.
  unfold R.v41390, N.v41390.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41391 (s : N.State) (i : N.Inputs) :
  R.v41391 (state s) (inputs i) = Zmod.unsigned (N.v41391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41391 s i)) at 1.
  unfold R.v41391, N.v41391.
  rewrite ?node_8876.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41392 (s : N.State) (i : N.Inputs) :
  R.v41392 (state s) (inputs i) = Zmod.unsigned (N.v41392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41392 s i)) at 1.
  unfold R.v41392, N.v41392.
  unfold R.v6, N.v6.
  rewrite !state_r838_nr_5F838.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r838_nr_5F838 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41393 (s : N.State) (i : N.Inputs) :
  R.v41393 (state s) (inputs i) = Zmod.unsigned (N.v41393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41393 s i)) at 1.
  unfold R.v41393, N.v41393.
  unfold R.v6, N.v6.
  rewrite ?node_8872.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41394 (s : N.State) (i : N.Inputs) :
  R.v41394 (state s) (inputs i) = Zmod.unsigned (N.v41394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41394 s i)) at 1.
  unfold R.v41394, N.v41394.
  rewrite ?node_41392.
  rewrite ?node_41393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41395 (s : N.State) (i : N.Inputs) :
  R.v41395 (state s) (inputs i) = Zmod.unsigned (N.v41395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41395 s i)) at 1.
  unfold R.v41395, N.v41395.
  unfold R.v16484, N.v16484.
  rewrite ?node_41394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41396 (s : N.State) (i : N.Inputs) :
  R.v41396 (state s) (inputs i) = Zmod.unsigned (N.v41396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41396 s i)) at 1.
  unfold R.v41396, N.v41396.
  rewrite ?node_41391.
  rewrite ?node_41395.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41397 (s : N.State) (i : N.Inputs) :
  R.v41397 (state s) (inputs i) = Zmod.unsigned (N.v41397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41397 s i)) at 1.
  unfold R.v41397, N.v41397.
  unfold R.v6, N.v6.
  rewrite ?node_41396.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41398 (s : N.State) (i : N.Inputs) :
  R.v41398 (state s) (inputs i) = Zmod.unsigned (N.v41398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41398 s i)) at 1.
  unfold R.v41398, N.v41398.
  rewrite ?node_8877.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41399 (s : N.State) (i : N.Inputs) :
  R.v41399 (state s) (inputs i) = Zmod.unsigned (N.v41399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41399 s i)) at 1.
  unfold R.v41399, N.v41399.
  unfold R.v6, N.v6.
  rewrite ?node_9057.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41400 (s : N.State) (i : N.Inputs) :
  R.v41400 (state s) (inputs i) = Zmod.unsigned (N.v41400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41400 s i)) at 1.
  unfold R.v41400, N.v41400.
  rewrite ?node_41398.
  rewrite ?node_41399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41401 (s : N.State) (i : N.Inputs) :
  R.v41401 (state s) (inputs i) = Zmod.unsigned (N.v41401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41401 s i)) at 1.
  unfold R.v41401, N.v41401.
  rewrite ?node_41397.
  rewrite ?node_41400.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41402 (s : N.State) (i : N.Inputs) :
  R.v41402 (state s) (inputs i) = Zmod.unsigned (N.v41402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41402 s i)) at 1.
  unfold R.v41402, N.v41402.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41403 (s : N.State) (i : N.Inputs) :
  R.v41403 (state s) (inputs i) = Zmod.unsigned (N.v41403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41403 s i)) at 1.
  unfold R.v41403, N.v41403.
  rewrite ?node_8896.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41404 (s : N.State) (i : N.Inputs) :
  R.v41404 (state s) (inputs i) = Zmod.unsigned (N.v41404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41404 s i)) at 1.
  unfold R.v41404, N.v41404.
  rewrite ?node_8892.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41405 (s : N.State) (i : N.Inputs) :
  R.v41405 (state s) (inputs i) = Zmod.unsigned (N.v41405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41405 s i)) at 1.
  unfold R.v41405, N.v41405.
  rewrite ?node_8888.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41406 (s : N.State) (i : N.Inputs) :
  R.v41406 (state s) (inputs i) = Zmod.unsigned (N.v41406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41406 s i)) at 1.
  unfold R.v41406, N.v41406.
  unfold R.v6, N.v6.
  rewrite ?node_8884.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41407 (s : N.State) (i : N.Inputs) :
  R.v41407 (state s) (inputs i) = Zmod.unsigned (N.v41407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41407 s i)) at 1.
  unfold R.v41407, N.v41407.
  unfold R.v6, N.v6.
  rewrite ?node_8881.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41408 (s : N.State) (i : N.Inputs) :
  R.v41408 (state s) (inputs i) = Zmod.unsigned (N.v41408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41408 s i)) at 1.
  unfold R.v41408, N.v41408.
  rewrite ?node_41406.
  rewrite ?node_41407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41409 (s : N.State) (i : N.Inputs) :
  R.v41409 (state s) (inputs i) = Zmod.unsigned (N.v41409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41409 s i)) at 1.
  unfold R.v41409, N.v41409.
  unfold R.v16484, N.v16484.
  rewrite ?node_41408.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41410 (s : N.State) (i : N.Inputs) :
  R.v41410 (state s) (inputs i) = Zmod.unsigned (N.v41410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41410 s i)) at 1.
  unfold R.v41410, N.v41410.
  rewrite ?node_41403.
  rewrite ?node_41404.
  rewrite ?node_41405.
  rewrite ?node_41409.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41411 (s : N.State) (i : N.Inputs) :
  R.v41411 (state s) (inputs i) = Zmod.unsigned (N.v41411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41411 s i)) at 1.
  unfold R.v41411, N.v41411.
  unfold R.v6, N.v6.
  rewrite ?node_41410.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41412 (s : N.State) (i : N.Inputs) :
  R.v41412 (state s) (inputs i) = Zmod.unsigned (N.v41412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41412 s i)) at 1.
  unfold R.v41412, N.v41412.
  rewrite ?node_8897.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41413 (s : N.State) (i : N.Inputs) :
  R.v41413 (state s) (inputs i) = Zmod.unsigned (N.v41413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41413 s i)) at 1.
  unfold R.v41413, N.v41413.
  unfold R.v6, N.v6.
  rewrite ?node_9033.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41414 (s : N.State) (i : N.Inputs) :
  R.v41414 (state s) (inputs i) = Zmod.unsigned (N.v41414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41414 s i)) at 1.
  unfold R.v41414, N.v41414.
  unfold R.v6, N.v6.
  rewrite ?node_9061.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41415 (s : N.State) (i : N.Inputs) :
  R.v41415 (state s) (inputs i) = Zmod.unsigned (N.v41415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41415 s i)) at 1.
  unfold R.v41415, N.v41415.
  rewrite ?node_41412.
  rewrite ?node_41413.
  rewrite ?node_41414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41416 (s : N.State) (i : N.Inputs) :
  R.v41416 (state s) (inputs i) = Zmod.unsigned (N.v41416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41416 s i)) at 1.
  unfold R.v41416, N.v41416.
  rewrite ?node_41411.
  rewrite ?node_41415.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41417 (s : N.State) (i : N.Inputs) :
  R.v41417 (state s) (inputs i) = Zmod.unsigned (N.v41417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41417 s i)) at 1.
  unfold R.v41417, N.v41417.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41418 (s : N.State) (i : N.Inputs) :
  R.v41418 (state s) (inputs i) = Zmod.unsigned (N.v41418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41418 s i)) at 1.
  unfold R.v41418, N.v41418.
  rewrite ?node_8888.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41419 (s : N.State) (i : N.Inputs) :
  R.v41419 (state s) (inputs i) = Zmod.unsigned (N.v41419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41419 s i)) at 1.
  unfold R.v41419, N.v41419.
  unfold R.v6, N.v6.
  rewrite ?node_8884.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41420 (s : N.State) (i : N.Inputs) :
  R.v41420 (state s) (inputs i) = Zmod.unsigned (N.v41420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41420 s i)) at 1.
  unfold R.v41420, N.v41420.
  unfold R.v6, N.v6.
  rewrite ?node_8881.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41421 (s : N.State) (i : N.Inputs) :
  R.v41421 (state s) (inputs i) = Zmod.unsigned (N.v41421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41421 s i)) at 1.
  unfold R.v41421, N.v41421.
  rewrite ?node_41419.
  rewrite ?node_41420.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41422 (s : N.State) (i : N.Inputs) :
  R.v41422 (state s) (inputs i) = Zmod.unsigned (N.v41422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41422 s i)) at 1.
  unfold R.v41422, N.v41422.
  unfold R.v16484, N.v16484.
  rewrite ?node_41421.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41423 (s : N.State) (i : N.Inputs) :
  R.v41423 (state s) (inputs i) = Zmod.unsigned (N.v41423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41423 s i)) at 1.
  unfold R.v41423, N.v41423.
  rewrite ?node_41418.
  rewrite ?node_41422.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41424 (s : N.State) (i : N.Inputs) :
  R.v41424 (state s) (inputs i) = Zmod.unsigned (N.v41424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41424 s i)) at 1.
  unfold R.v41424, N.v41424.
  unfold R.v6, N.v6.
  rewrite ?node_41423.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41425 (s : N.State) (i : N.Inputs) :
  R.v41425 (state s) (inputs i) = Zmod.unsigned (N.v41425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41425 s i)) at 1.
  unfold R.v41425, N.v41425.
  rewrite ?node_8889.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41426 (s : N.State) (i : N.Inputs) :
  R.v41426 (state s) (inputs i) = Zmod.unsigned (N.v41426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41426 s i)) at 1.
  unfold R.v41426, N.v41426.
  unfold R.v6, N.v6.
  rewrite ?node_9033.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41427 (s : N.State) (i : N.Inputs) :
  R.v41427 (state s) (inputs i) = Zmod.unsigned (N.v41427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41427 s i)) at 1.
  unfold R.v41427, N.v41427.
  rewrite ?node_41425.
  rewrite ?node_41426.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41428 (s : N.State) (i : N.Inputs) :
  R.v41428 (state s) (inputs i) = Zmod.unsigned (N.v41428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41428 s i)) at 1.
  unfold R.v41428, N.v41428.
  rewrite ?node_41424.
  rewrite ?node_41427.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41429 (s : N.State) (i : N.Inputs) :
  R.v41429 (state s) (inputs i) = Zmod.unsigned (N.v41429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41429 s i)) at 1.
  unfold R.v41429, N.v41429.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41430 (s : N.State) (i : N.Inputs) :
  R.v41430 (state s) (inputs i) = Zmod.unsigned (N.v41430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41430 s i)) at 1.
  unfold R.v41430, N.v41430.
  rewrite ?node_8896.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41431 (s : N.State) (i : N.Inputs) :
  R.v41431 (state s) (inputs i) = Zmod.unsigned (N.v41431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41431 s i)) at 1.
  unfold R.v41431, N.v41431.
  unfold R.v6, N.v6.
  rewrite ?node_8892.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41432 (s : N.State) (i : N.Inputs) :
  R.v41432 (state s) (inputs i) = Zmod.unsigned (N.v41432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41432 s i)) at 1.
  unfold R.v41432, N.v41432.
  unfold R.v6, N.v6.
  rewrite ?node_8889.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41433 (s : N.State) (i : N.Inputs) :
  R.v41433 (state s) (inputs i) = Zmod.unsigned (N.v41433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41433 s i)) at 1.
  unfold R.v41433, N.v41433.
  rewrite ?node_41431.
  rewrite ?node_41432.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41434 (s : N.State) (i : N.Inputs) :
  R.v41434 (state s) (inputs i) = Zmod.unsigned (N.v41434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41434 s i)) at 1.
  unfold R.v41434, N.v41434.
  unfold R.v16484, N.v16484.
  rewrite ?node_41433.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41435 (s : N.State) (i : N.Inputs) :
  R.v41435 (state s) (inputs i) = Zmod.unsigned (N.v41435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41435 s i)) at 1.
  unfold R.v41435, N.v41435.
  rewrite ?node_41430.
  rewrite ?node_41434.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41436 (s : N.State) (i : N.Inputs) :
  R.v41436 (state s) (inputs i) = Zmod.unsigned (N.v41436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41436 s i)) at 1.
  unfold R.v41436, N.v41436.
  unfold R.v6, N.v6.
  rewrite ?node_41435.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41437 (s : N.State) (i : N.Inputs) :
  R.v41437 (state s) (inputs i) = Zmod.unsigned (N.v41437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41437 s i)) at 1.
  unfold R.v41437, N.v41437.
  rewrite ?node_8897.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41438 (s : N.State) (i : N.Inputs) :
  R.v41438 (state s) (inputs i) = Zmod.unsigned (N.v41438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41438 s i)) at 1.
  unfold R.v41438, N.v41438.
  unfold R.v6, N.v6.
  rewrite ?node_9061.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41439 (s : N.State) (i : N.Inputs) :
  R.v41439 (state s) (inputs i) = Zmod.unsigned (N.v41439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41439 s i)) at 1.
  unfold R.v41439, N.v41439.
  rewrite ?node_41437.
  rewrite ?node_41438.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41440 (s : N.State) (i : N.Inputs) :
  R.v41440 (state s) (inputs i) = Zmod.unsigned (N.v41440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41440 s i)) at 1.
  unfold R.v41440, N.v41440.
  rewrite ?node_41436.
  rewrite ?node_41439.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41441 (s : N.State) (i : N.Inputs) :
  R.v41441 (state s) (inputs i) = Zmod.unsigned (N.v41441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41441 s i)) at 1.
  unfold R.v41441, N.v41441.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41442 (s : N.State) (i : N.Inputs) :
  R.v41442 (state s) (inputs i) = Zmod.unsigned (N.v41442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41442 s i)) at 1.
  unfold R.v41442, N.v41442.
  rewrite ?node_8908.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41443 (s : N.State) (i : N.Inputs) :
  R.v41443 (state s) (inputs i) = Zmod.unsigned (N.v41443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41443 s i)) at 1.
  unfold R.v41443, N.v41443.
  unfold R.v6, N.v6.
  rewrite ?node_8904.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41444 (s : N.State) (i : N.Inputs) :
  R.v41444 (state s) (inputs i) = Zmod.unsigned (N.v41444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41444 s i)) at 1.
  unfold R.v41444, N.v41444.
  unfold R.v6, N.v6.
  rewrite ?node_8901.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41445 (s : N.State) (i : N.Inputs) :
  R.v41445 (state s) (inputs i) = Zmod.unsigned (N.v41445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41445 s i)) at 1.
  unfold R.v41445, N.v41445.
  rewrite ?node_41443.
  rewrite ?node_41444.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41446 (s : N.State) (i : N.Inputs) :
  R.v41446 (state s) (inputs i) = Zmod.unsigned (N.v41446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41446 s i)) at 1.
  unfold R.v41446, N.v41446.
  unfold R.v16484, N.v16484.
  rewrite ?node_41445.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41447 (s : N.State) (i : N.Inputs) :
  R.v41447 (state s) (inputs i) = Zmod.unsigned (N.v41447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41447 s i)) at 1.
  unfold R.v41447, N.v41447.
  rewrite ?node_41442.
  rewrite ?node_41446.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41448 (s : N.State) (i : N.Inputs) :
  R.v41448 (state s) (inputs i) = Zmod.unsigned (N.v41448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41448 s i)) at 1.
  unfold R.v41448, N.v41448.
  unfold R.v6, N.v6.
  rewrite ?node_41447.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41449 (s : N.State) (i : N.Inputs) :
  R.v41449 (state s) (inputs i) = Zmod.unsigned (N.v41449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41449 s i)) at 1.
  unfold R.v41449, N.v41449.
  rewrite ?node_8909.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41450 (s : N.State) (i : N.Inputs) :
  R.v41450 (state s) (inputs i) = Zmod.unsigned (N.v41450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41450 s i)) at 1.
  unfold R.v41450, N.v41450.
  unfold R.v6, N.v6.
  rewrite ?node_9065.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41451 (s : N.State) (i : N.Inputs) :
  R.v41451 (state s) (inputs i) = Zmod.unsigned (N.v41451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41451 s i)) at 1.
  unfold R.v41451, N.v41451.
  rewrite ?node_41449.
  rewrite ?node_41450.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41452 (s : N.State) (i : N.Inputs) :
  R.v41452 (state s) (inputs i) = Zmod.unsigned (N.v41452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41452 s i)) at 1.
  unfold R.v41452, N.v41452.
  rewrite ?node_41448.
  rewrite ?node_41451.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41453 (s : N.State) (i : N.Inputs) :
  R.v41453 (state s) (inputs i) = Zmod.unsigned (N.v41453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41453 s i)) at 1.
  unfold R.v41453, N.v41453.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41454 (s : N.State) (i : N.Inputs) :
  R.v41454 (state s) (inputs i) = Zmod.unsigned (N.v41454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41454 s i)) at 1.
  unfold R.v41454, N.v41454.
  rewrite ?node_8985.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41455 (s : N.State) (i : N.Inputs) :
  R.v41455 (state s) (inputs i) = Zmod.unsigned (N.v41455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41455 s i)) at 1.
  unfold R.v41455, N.v41455.
  rewrite ?node_8981.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41456 (s : N.State) (i : N.Inputs) :
  R.v41456 (state s) (inputs i) = Zmod.unsigned (N.v41456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41456 s i)) at 1.
  unfold R.v41456, N.v41456.
  rewrite ?node_8973.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41457 (s : N.State) (i : N.Inputs) :
  R.v41457 (state s) (inputs i) = Zmod.unsigned (N.v41457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41457 s i)) at 1.
  unfold R.v41457, N.v41457.
  unfold R.v6, N.v6.
  rewrite ?node_8965.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41458 (s : N.State) (i : N.Inputs) :
  R.v41458 (state s) (inputs i) = Zmod.unsigned (N.v41458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41458 s i)) at 1.
  unfold R.v41458, N.v41458.
  unfold R.v6, N.v6.
  rewrite ?node_8958.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41459 (s : N.State) (i : N.Inputs) :
  R.v41459 (state s) (inputs i) = Zmod.unsigned (N.v41459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41459 s i)) at 1.
  unfold R.v41459, N.v41459.
  rewrite ?node_41457.
  rewrite ?node_41458.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41460 (s : N.State) (i : N.Inputs) :
  R.v41460 (state s) (inputs i) = Zmod.unsigned (N.v41460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41460 s i)) at 1.
  unfold R.v41460, N.v41460.
  unfold R.v16484, N.v16484.
  rewrite ?node_41459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41461 (s : N.State) (i : N.Inputs) :
  R.v41461 (state s) (inputs i) = Zmod.unsigned (N.v41461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41461 s i)) at 1.
  unfold R.v41461, N.v41461.
  rewrite ?node_41454.
  rewrite ?node_41455.
  rewrite ?node_41456.
  rewrite ?node_41460.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41462 (s : N.State) (i : N.Inputs) :
  R.v41462 (state s) (inputs i) = Zmod.unsigned (N.v41462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41462 s i)) at 1.
  unfold R.v41462, N.v41462.
  unfold R.v6, N.v6.
  rewrite ?node_41461.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41463 (s : N.State) (i : N.Inputs) :
  R.v41463 (state s) (inputs i) = Zmod.unsigned (N.v41463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41463 s i)) at 1.
  unfold R.v41463, N.v41463.
  rewrite ?node_8986.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41464 (s : N.State) (i : N.Inputs) :
  R.v41464 (state s) (inputs i) = Zmod.unsigned (N.v41464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41464 s i)) at 1.
  unfold R.v41464, N.v41464.
  unfold R.v6, N.v6.
  rewrite ?node_9124.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41465 (s : N.State) (i : N.Inputs) :
  R.v41465 (state s) (inputs i) = Zmod.unsigned (N.v41465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41465 s i)) at 1.
  unfold R.v41465, N.v41465.
  unfold R.v6, N.v6.
  rewrite ?node_9194.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41466 (s : N.State) (i : N.Inputs) :
  R.v41466 (state s) (inputs i) = Zmod.unsigned (N.v41466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41466 s i)) at 1.
  unfold R.v41466, N.v41466.
  rewrite ?node_41463.
  rewrite ?node_41464.
  rewrite ?node_41465.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41467 (s : N.State) (i : N.Inputs) :
  R.v41467 (state s) (inputs i) = Zmod.unsigned (N.v41467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41467 s i)) at 1.
  unfold R.v41467, N.v41467.
  rewrite ?node_41462.
  rewrite ?node_41466.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41468 (s : N.State) (i : N.Inputs) :
  R.v41468 (state s) (inputs i) = Zmod.unsigned (N.v41468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41468 s i)) at 1.
  unfold R.v41468, N.v41468.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41469 (s : N.State) (i : N.Inputs) :
  R.v41469 (state s) (inputs i) = Zmod.unsigned (N.v41469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41469 s i)) at 1.
  unfold R.v41469, N.v41469.
  rewrite ?node_8973.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41470 (s : N.State) (i : N.Inputs) :
  R.v41470 (state s) (inputs i) = Zmod.unsigned (N.v41470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41470 s i)) at 1.
  unfold R.v41470, N.v41470.
  unfold R.v6, N.v6.
  rewrite ?node_8965.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41471 (s : N.State) (i : N.Inputs) :
  R.v41471 (state s) (inputs i) = Zmod.unsigned (N.v41471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41471 s i)) at 1.
  unfold R.v41471, N.v41471.
  unfold R.v6, N.v6.
  rewrite ?node_8958.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41472 (s : N.State) (i : N.Inputs) :
  R.v41472 (state s) (inputs i) = Zmod.unsigned (N.v41472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41472 s i)) at 1.
  unfold R.v41472, N.v41472.
  rewrite ?node_41470.
  rewrite ?node_41471.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41473 (s : N.State) (i : N.Inputs) :
  R.v41473 (state s) (inputs i) = Zmod.unsigned (N.v41473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41473 s i)) at 1.
  unfold R.v41473, N.v41473.
  unfold R.v16484, N.v16484.
  rewrite ?node_41472.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41474 (s : N.State) (i : N.Inputs) :
  R.v41474 (state s) (inputs i) = Zmod.unsigned (N.v41474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41474 s i)) at 1.
  unfold R.v41474, N.v41474.
  rewrite ?node_41469.
  rewrite ?node_41473.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41475 (s : N.State) (i : N.Inputs) :
  R.v41475 (state s) (inputs i) = Zmod.unsigned (N.v41475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41475 s i)) at 1.
  unfold R.v41475, N.v41475.
  unfold R.v6, N.v6.
  rewrite ?node_41474.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41476 (s : N.State) (i : N.Inputs) :
  R.v41476 (state s) (inputs i) = Zmod.unsigned (N.v41476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41476 s i)) at 1.
  unfold R.v41476, N.v41476.
  rewrite ?node_8974.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41477 (s : N.State) (i : N.Inputs) :
  R.v41477 (state s) (inputs i) = Zmod.unsigned (N.v41477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41477 s i)) at 1.
  unfold R.v41477, N.v41477.
  unfold R.v6, N.v6.
  rewrite ?node_9124.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41478 (s : N.State) (i : N.Inputs) :
  R.v41478 (state s) (inputs i) = Zmod.unsigned (N.v41478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41478 s i)) at 1.
  unfold R.v41478, N.v41478.
  rewrite ?node_41476.
  rewrite ?node_41477.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41479 (s : N.State) (i : N.Inputs) :
  R.v41479 (state s) (inputs i) = Zmod.unsigned (N.v41479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41479 s i)) at 1.
  unfold R.v41479, N.v41479.
  rewrite ?node_41475.
  rewrite ?node_41478.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41480 (s : N.State) (i : N.Inputs) :
  R.v41480 (state s) (inputs i) = Zmod.unsigned (N.v41480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41480 s i)) at 1.
  unfold R.v41480, N.v41480.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41481 (s : N.State) (i : N.Inputs) :
  R.v41481 (state s) (inputs i) = Zmod.unsigned (N.v41481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41481 s i)) at 1.
  unfold R.v41481, N.v41481.
  rewrite ?node_8985.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41482 (s : N.State) (i : N.Inputs) :
  R.v41482 (state s) (inputs i) = Zmod.unsigned (N.v41482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41482 s i)) at 1.
  unfold R.v41482, N.v41482.
  unfold R.v6, N.v6.
  rewrite ?node_8981.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41483 (s : N.State) (i : N.Inputs) :
  R.v41483 (state s) (inputs i) = Zmod.unsigned (N.v41483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41483 s i)) at 1.
  unfold R.v41483, N.v41483.
  unfold R.v6, N.v6.
  rewrite ?node_8974.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41484 (s : N.State) (i : N.Inputs) :
  R.v41484 (state s) (inputs i) = Zmod.unsigned (N.v41484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41484 s i)) at 1.
  unfold R.v41484, N.v41484.
  rewrite ?node_41482.
  rewrite ?node_41483.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41485 (s : N.State) (i : N.Inputs) :
  R.v41485 (state s) (inputs i) = Zmod.unsigned (N.v41485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41485 s i)) at 1.
  unfold R.v41485, N.v41485.
  unfold R.v16484, N.v16484.
  rewrite ?node_41484.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41486 (s : N.State) (i : N.Inputs) :
  R.v41486 (state s) (inputs i) = Zmod.unsigned (N.v41486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41486 s i)) at 1.
  unfold R.v41486, N.v41486.
  rewrite ?node_41481.
  rewrite ?node_41485.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41487 (s : N.State) (i : N.Inputs) :
  R.v41487 (state s) (inputs i) = Zmod.unsigned (N.v41487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41487 s i)) at 1.
  unfold R.v41487, N.v41487.
  unfold R.v6, N.v6.
  rewrite ?node_41486.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41488 (s : N.State) (i : N.Inputs) :
  R.v41488 (state s) (inputs i) = Zmod.unsigned (N.v41488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41488 s i)) at 1.
  unfold R.v41488, N.v41488.
  rewrite ?node_8986.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41489 (s : N.State) (i : N.Inputs) :
  R.v41489 (state s) (inputs i) = Zmod.unsigned (N.v41489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41489 s i)) at 1.
  unfold R.v41489, N.v41489.
  unfold R.v6, N.v6.
  rewrite ?node_9194.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41490 (s : N.State) (i : N.Inputs) :
  R.v41490 (state s) (inputs i) = Zmod.unsigned (N.v41490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41490 s i)) at 1.
  unfold R.v41490, N.v41490.
  rewrite ?node_41488.
  rewrite ?node_41489.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41491 (s : N.State) (i : N.Inputs) :
  R.v41491 (state s) (inputs i) = Zmod.unsigned (N.v41491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41491 s i)) at 1.
  unfold R.v41491, N.v41491.
  rewrite ?node_41487.
  rewrite ?node_41490.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41492 (s : N.State) (i : N.Inputs) :
  R.v41492 (state s) (inputs i) = Zmod.unsigned (N.v41492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41492 s i)) at 1.
  unfold R.v41492, N.v41492.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41493 (s : N.State) (i : N.Inputs) :
  R.v41493 (state s) (inputs i) = Zmod.unsigned (N.v41493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41493 s i)) at 1.
  unfold R.v41493, N.v41493.
  rewrite ?node_9013.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41494 (s : N.State) (i : N.Inputs) :
  R.v41494 (state s) (inputs i) = Zmod.unsigned (N.v41494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41494 s i)) at 1.
  unfold R.v41494, N.v41494.
  unfold R.v16463, N.v16463.
  rewrite !state_r867_nr_5F867.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r867_nr_5F867 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41495 (s : N.State) (i : N.Inputs) :
  R.v41495 (state s) (inputs i) = Zmod.unsigned (N.v41495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41495 s i)) at 1.
  unfold R.v41495, N.v41495.
  rewrite ?node_9008.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41496 (s : N.State) (i : N.Inputs) :
  R.v41496 (state s) (inputs i) = Zmod.unsigned (N.v41496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41496 s i)) at 1.
  unfold R.v41496, N.v41496.
  unfold R.v6, N.v6.
  rewrite ?node_9000.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41497 (s : N.State) (i : N.Inputs) :
  R.v41497 (state s) (inputs i) = Zmod.unsigned (N.v41497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41497 s i)) at 1.
  unfold R.v41497, N.v41497.
  unfold R.v6, N.v6.
  rewrite ?node_8993.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41498 (s : N.State) (i : N.Inputs) :
  R.v41498 (state s) (inputs i) = Zmod.unsigned (N.v41498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41498 s i)) at 1.
  unfold R.v41498, N.v41498.
  rewrite ?node_41496.
  rewrite ?node_41497.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41499 (s : N.State) (i : N.Inputs) :
  R.v41499 (state s) (inputs i) = Zmod.unsigned (N.v41499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41499 s i)) at 1.
  unfold R.v41499, N.v41499.
  unfold R.v16484, N.v16484.
  rewrite ?node_41498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41500 (s : N.State) (i : N.Inputs) :
  R.v41500 (state s) (inputs i) = Zmod.unsigned (N.v41500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41500 s i)) at 1.
  unfold R.v41500, N.v41500.
  rewrite ?node_41493.
  rewrite ?node_41494.
  rewrite ?node_41495.
  rewrite ?node_41499.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41501 (s : N.State) (i : N.Inputs) :
  R.v41501 (state s) (inputs i) = Zmod.unsigned (N.v41501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41501 s i)) at 1.
  unfold R.v41501, N.v41501.
  unfold R.v6, N.v6.
  rewrite ?node_41500.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41502 (s : N.State) (i : N.Inputs) :
  R.v41502 (state s) (inputs i) = Zmod.unsigned (N.v41502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41502 s i)) at 1.
  unfold R.v41502, N.v41502.
  rewrite ?node_9014.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41503 (s : N.State) (i : N.Inputs) :
  R.v41503 (state s) (inputs i) = Zmod.unsigned (N.v41503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41503 s i)) at 1.
  unfold R.v41503, N.v41503.
  unfold R.v6, N.v6.
  rewrite ?node_9153.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41504 (s : N.State) (i : N.Inputs) :
  R.v41504 (state s) (inputs i) = Zmod.unsigned (N.v41504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41504 s i)) at 1.
  unfold R.v41504, N.v41504.
  unfold R.v6, N.v6.
  rewrite ?node_9197.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41505 (s : N.State) (i : N.Inputs) :
  R.v41505 (state s) (inputs i) = Zmod.unsigned (N.v41505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41505 s i)) at 1.
  unfold R.v41505, N.v41505.
  rewrite ?node_41502.
  rewrite ?node_41503.
  rewrite ?node_41504.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41506 (s : N.State) (i : N.Inputs) :
  R.v41506 (state s) (inputs i) = Zmod.unsigned (N.v41506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41506 s i)) at 1.
  unfold R.v41506, N.v41506.
  rewrite ?node_41501.
  rewrite ?node_41505.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41507 (s : N.State) (i : N.Inputs) :
  R.v41507 (state s) (inputs i) = Zmod.unsigned (N.v41507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41507 s i)) at 1.
  unfold R.v41507, N.v41507.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41508 (s : N.State) (i : N.Inputs) :
  R.v41508 (state s) (inputs i) = Zmod.unsigned (N.v41508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41508 s i)) at 1.
  unfold R.v41508, N.v41508.
  rewrite ?node_9008.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41509 (s : N.State) (i : N.Inputs) :
  R.v41509 (state s) (inputs i) = Zmod.unsigned (N.v41509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41509 s i)) at 1.
  unfold R.v41509, N.v41509.
  unfold R.v6, N.v6.
  rewrite ?node_9000.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41510 (s : N.State) (i : N.Inputs) :
  R.v41510 (state s) (inputs i) = Zmod.unsigned (N.v41510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41510 s i)) at 1.
  unfold R.v41510, N.v41510.
  unfold R.v6, N.v6.
  rewrite ?node_8993.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41511 (s : N.State) (i : N.Inputs) :
  R.v41511 (state s) (inputs i) = Zmod.unsigned (N.v41511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41511 s i)) at 1.
  unfold R.v41511, N.v41511.
  rewrite ?node_41509.
  rewrite ?node_41510.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41512 (s : N.State) (i : N.Inputs) :
  R.v41512 (state s) (inputs i) = Zmod.unsigned (N.v41512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41512 s i)) at 1.
  unfold R.v41512, N.v41512.
  unfold R.v16484, N.v16484.
  rewrite ?node_41511.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41513 (s : N.State) (i : N.Inputs) :
  R.v41513 (state s) (inputs i) = Zmod.unsigned (N.v41513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41513 s i)) at 1.
  unfold R.v41513, N.v41513.
  rewrite ?node_41508.
  rewrite ?node_41512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41514 (s : N.State) (i : N.Inputs) :
  R.v41514 (state s) (inputs i) = Zmod.unsigned (N.v41514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41514 s i)) at 1.
  unfold R.v41514, N.v41514.
  unfold R.v6, N.v6.
  rewrite ?node_41513.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41515 (s : N.State) (i : N.Inputs) :
  R.v41515 (state s) (inputs i) = Zmod.unsigned (N.v41515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41515 s i)) at 1.
  unfold R.v41515, N.v41515.
  rewrite ?node_9009.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41516 (s : N.State) (i : N.Inputs) :
  R.v41516 (state s) (inputs i) = Zmod.unsigned (N.v41516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41516 s i)) at 1.
  unfold R.v41516, N.v41516.
  unfold R.v6, N.v6.
  rewrite ?node_9153.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41517 (s : N.State) (i : N.Inputs) :
  R.v41517 (state s) (inputs i) = Zmod.unsigned (N.v41517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41517 s i)) at 1.
  unfold R.v41517, N.v41517.
  rewrite ?node_41515.
  rewrite ?node_41516.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41518 (s : N.State) (i : N.Inputs) :
  R.v41518 (state s) (inputs i) = Zmod.unsigned (N.v41518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41518 s i)) at 1.
  unfold R.v41518, N.v41518.
  rewrite ?node_41514.
  rewrite ?node_41517.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41519 (s : N.State) (i : N.Inputs) :
  R.v41519 (state s) (inputs i) = Zmod.unsigned (N.v41519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41519 s i)) at 1.
  unfold R.v41519, N.v41519.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41520 (s : N.State) (i : N.Inputs) :
  R.v41520 (state s) (inputs i) = Zmod.unsigned (N.v41520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41520 s i)) at 1.
  unfold R.v41520, N.v41520.
  rewrite ?node_9013.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41521 (s : N.State) (i : N.Inputs) :
  R.v41521 (state s) (inputs i) = Zmod.unsigned (N.v41521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41521 s i)) at 1.
  unfold R.v41521, N.v41521.
  unfold R.v6, N.v6.
  rewrite !state_r867_nr_5F867.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r867_nr_5F867 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41522 (s : N.State) (i : N.Inputs) :
  R.v41522 (state s) (inputs i) = Zmod.unsigned (N.v41522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41522 s i)) at 1.
  unfold R.v41522, N.v41522.
  unfold R.v6, N.v6.
  rewrite ?node_9009.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41523 (s : N.State) (i : N.Inputs) :
  R.v41523 (state s) (inputs i) = Zmod.unsigned (N.v41523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41523 s i)) at 1.
  unfold R.v41523, N.v41523.
  rewrite ?node_41521.
  rewrite ?node_41522.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41524 (s : N.State) (i : N.Inputs) :
  R.v41524 (state s) (inputs i) = Zmod.unsigned (N.v41524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41524 s i)) at 1.
  unfold R.v41524, N.v41524.
  unfold R.v16484, N.v16484.
  rewrite ?node_41523.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41525 (s : N.State) (i : N.Inputs) :
  R.v41525 (state s) (inputs i) = Zmod.unsigned (N.v41525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41525 s i)) at 1.
  unfold R.v41525, N.v41525.
  rewrite ?node_41520.
  rewrite ?node_41524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41526 (s : N.State) (i : N.Inputs) :
  R.v41526 (state s) (inputs i) = Zmod.unsigned (N.v41526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41526 s i)) at 1.
  unfold R.v41526, N.v41526.
  unfold R.v6, N.v6.
  rewrite ?node_41525.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41527 (s : N.State) (i : N.Inputs) :
  R.v41527 (state s) (inputs i) = Zmod.unsigned (N.v41527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41527 s i)) at 1.
  unfold R.v41527, N.v41527.
  rewrite ?node_9014.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41528 (s : N.State) (i : N.Inputs) :
  R.v41528 (state s) (inputs i) = Zmod.unsigned (N.v41528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41528 s i)) at 1.
  unfold R.v41528, N.v41528.
  unfold R.v6, N.v6.
  rewrite ?node_9197.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41529 (s : N.State) (i : N.Inputs) :
  R.v41529 (state s) (inputs i) = Zmod.unsigned (N.v41529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41529 s i)) at 1.
  unfold R.v41529, N.v41529.
  rewrite ?node_41527.
  rewrite ?node_41528.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41530 (s : N.State) (i : N.Inputs) :
  R.v41530 (state s) (inputs i) = Zmod.unsigned (N.v41530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41530 s i)) at 1.
  unfold R.v41530, N.v41530.
  rewrite ?node_41526.
  rewrite ?node_41529.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41531 (s : N.State) (i : N.Inputs) :
  R.v41531 (state s) (inputs i) = Zmod.unsigned (N.v41531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41531 s i)) at 1.
  unfold R.v41531, N.v41531.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41532 (s : N.State) (i : N.Inputs) :
  R.v41532 (state s) (inputs i) = Zmod.unsigned (N.v41532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41532 s i)) at 1.
  unfold R.v41532, N.v41532.
  rewrite ?node_9033.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41533 (s : N.State) (i : N.Inputs) :
  R.v41533 (state s) (inputs i) = Zmod.unsigned (N.v41533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41533 s i)) at 1.
  unfold R.v41533, N.v41533.
  rewrite ?node_9029.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41534 (s : N.State) (i : N.Inputs) :
  R.v41534 (state s) (inputs i) = Zmod.unsigned (N.v41534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41534 s i)) at 1.
  unfold R.v41534, N.v41534.
  rewrite ?node_9025.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41535 (s : N.State) (i : N.Inputs) :
  R.v41535 (state s) (inputs i) = Zmod.unsigned (N.v41535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41535 s i)) at 1.
  unfold R.v41535, N.v41535.
  unfold R.v6, N.v6.
  rewrite ?node_9021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41536 (s : N.State) (i : N.Inputs) :
  R.v41536 (state s) (inputs i) = Zmod.unsigned (N.v41536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41536 s i)) at 1.
  unfold R.v41536, N.v41536.
  unfold R.v6, N.v6.
  rewrite ?node_9018.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41537 (s : N.State) (i : N.Inputs) :
  R.v41537 (state s) (inputs i) = Zmod.unsigned (N.v41537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41537 s i)) at 1.
  unfold R.v41537, N.v41537.
  rewrite ?node_41535.
  rewrite ?node_41536.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41538 (s : N.State) (i : N.Inputs) :
  R.v41538 (state s) (inputs i) = Zmod.unsigned (N.v41538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41538 s i)) at 1.
  unfold R.v41538, N.v41538.
  unfold R.v16484, N.v16484.
  rewrite ?node_41537.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41539 (s : N.State) (i : N.Inputs) :
  R.v41539 (state s) (inputs i) = Zmod.unsigned (N.v41539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41539 s i)) at 1.
  unfold R.v41539, N.v41539.
  rewrite ?node_41532.
  rewrite ?node_41533.
  rewrite ?node_41534.
  rewrite ?node_41538.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41540 (s : N.State) (i : N.Inputs) :
  R.v41540 (state s) (inputs i) = Zmod.unsigned (N.v41540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41540 s i)) at 1.
  unfold R.v41540, N.v41540.
  unfold R.v6, N.v6.
  rewrite ?node_41539.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41541 (s : N.State) (i : N.Inputs) :
  R.v41541 (state s) (inputs i) = Zmod.unsigned (N.v41541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41541 s i)) at 1.
  unfold R.v41541, N.v41541.
  rewrite ?node_9034.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41542 (s : N.State) (i : N.Inputs) :
  R.v41542 (state s) (inputs i) = Zmod.unsigned (N.v41542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41542 s i)) at 1.
  unfold R.v41542, N.v41542.
  unfold R.v6, N.v6.
  rewrite ?node_9173.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41543 (s : N.State) (i : N.Inputs) :
  R.v41543 (state s) (inputs i) = Zmod.unsigned (N.v41543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41543 s i)) at 1.
  unfold R.v41543, N.v41543.
  unfold R.v6, N.v6.
  rewrite ?node_9201.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41544 (s : N.State) (i : N.Inputs) :
  R.v41544 (state s) (inputs i) = Zmod.unsigned (N.v41544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41544 s i)) at 1.
  unfold R.v41544, N.v41544.
  rewrite ?node_41541.
  rewrite ?node_41542.
  rewrite ?node_41543.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41545 (s : N.State) (i : N.Inputs) :
  R.v41545 (state s) (inputs i) = Zmod.unsigned (N.v41545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41545 s i)) at 1.
  unfold R.v41545, N.v41545.
  rewrite ?node_41540.
  rewrite ?node_41544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41546 (s : N.State) (i : N.Inputs) :
  R.v41546 (state s) (inputs i) = Zmod.unsigned (N.v41546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41546 s i)) at 1.
  unfold R.v41546, N.v41546.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41547 (s : N.State) (i : N.Inputs) :
  R.v41547 (state s) (inputs i) = Zmod.unsigned (N.v41547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41547 s i)) at 1.
  unfold R.v41547, N.v41547.
  rewrite ?node_9025.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41548 (s : N.State) (i : N.Inputs) :
  R.v41548 (state s) (inputs i) = Zmod.unsigned (N.v41548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41548 s i)) at 1.
  unfold R.v41548, N.v41548.
  unfold R.v6, N.v6.
  rewrite ?node_9021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41549 (s : N.State) (i : N.Inputs) :
  R.v41549 (state s) (inputs i) = Zmod.unsigned (N.v41549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41549 s i)) at 1.
  unfold R.v41549, N.v41549.
  unfold R.v6, N.v6.
  rewrite ?node_9018.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41550 (s : N.State) (i : N.Inputs) :
  R.v41550 (state s) (inputs i) = Zmod.unsigned (N.v41550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41550 s i)) at 1.
  unfold R.v41550, N.v41550.
  rewrite ?node_41548.
  rewrite ?node_41549.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41551 (s : N.State) (i : N.Inputs) :
  R.v41551 (state s) (inputs i) = Zmod.unsigned (N.v41551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41551 s i)) at 1.
  unfold R.v41551, N.v41551.
  unfold R.v16484, N.v16484.
  rewrite ?node_41550.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41552 (s : N.State) (i : N.Inputs) :
  R.v41552 (state s) (inputs i) = Zmod.unsigned (N.v41552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41552 s i)) at 1.
  unfold R.v41552, N.v41552.
  rewrite ?node_41547.
  rewrite ?node_41551.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41553 (s : N.State) (i : N.Inputs) :
  R.v41553 (state s) (inputs i) = Zmod.unsigned (N.v41553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41553 s i)) at 1.
  unfold R.v41553, N.v41553.
  unfold R.v6, N.v6.
  rewrite ?node_41552.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41554 (s : N.State) (i : N.Inputs) :
  R.v41554 (state s) (inputs i) = Zmod.unsigned (N.v41554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41554 s i)) at 1.
  unfold R.v41554, N.v41554.
  rewrite ?node_9026.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41555 (s : N.State) (i : N.Inputs) :
  R.v41555 (state s) (inputs i) = Zmod.unsigned (N.v41555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41555 s i)) at 1.
  unfold R.v41555, N.v41555.
  unfold R.v6, N.v6.
  rewrite ?node_9173.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41556 (s : N.State) (i : N.Inputs) :
  R.v41556 (state s) (inputs i) = Zmod.unsigned (N.v41556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41556 s i)) at 1.
  unfold R.v41556, N.v41556.
  rewrite ?node_41554.
  rewrite ?node_41555.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41557 (s : N.State) (i : N.Inputs) :
  R.v41557 (state s) (inputs i) = Zmod.unsigned (N.v41557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41557 s i)) at 1.
  unfold R.v41557, N.v41557.
  rewrite ?node_41553.
  rewrite ?node_41556.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41558 (s : N.State) (i : N.Inputs) :
  R.v41558 (state s) (inputs i) = Zmod.unsigned (N.v41558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41558 s i)) at 1.
  unfold R.v41558, N.v41558.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41559 (s : N.State) (i : N.Inputs) :
  R.v41559 (state s) (inputs i) = Zmod.unsigned (N.v41559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41559 s i)) at 1.
  unfold R.v41559, N.v41559.
  rewrite ?node_9033.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41560 (s : N.State) (i : N.Inputs) :
  R.v41560 (state s) (inputs i) = Zmod.unsigned (N.v41560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41560 s i)) at 1.
  unfold R.v41560, N.v41560.
  unfold R.v6, N.v6.
  rewrite ?node_9029.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41561 (s : N.State) (i : N.Inputs) :
  R.v41561 (state s) (inputs i) = Zmod.unsigned (N.v41561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41561 s i)) at 1.
  unfold R.v41561, N.v41561.
  unfold R.v6, N.v6.
  rewrite ?node_9026.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41562 (s : N.State) (i : N.Inputs) :
  R.v41562 (state s) (inputs i) = Zmod.unsigned (N.v41562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41562 s i)) at 1.
  unfold R.v41562, N.v41562.
  rewrite ?node_41560.
  rewrite ?node_41561.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41563 (s : N.State) (i : N.Inputs) :
  R.v41563 (state s) (inputs i) = Zmod.unsigned (N.v41563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41563 s i)) at 1.
  unfold R.v41563, N.v41563.
  unfold R.v16484, N.v16484.
  rewrite ?node_41562.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41564 (s : N.State) (i : N.Inputs) :
  R.v41564 (state s) (inputs i) = Zmod.unsigned (N.v41564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41564 s i)) at 1.
  unfold R.v41564, N.v41564.
  rewrite ?node_41559.
  rewrite ?node_41563.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41565 (s : N.State) (i : N.Inputs) :
  R.v41565 (state s) (inputs i) = Zmod.unsigned (N.v41565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41565 s i)) at 1.
  unfold R.v41565, N.v41565.
  unfold R.v6, N.v6.
  rewrite ?node_41564.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41566 (s : N.State) (i : N.Inputs) :
  R.v41566 (state s) (inputs i) = Zmod.unsigned (N.v41566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41566 s i)) at 1.
  unfold R.v41566, N.v41566.
  rewrite ?node_9034.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41567 (s : N.State) (i : N.Inputs) :
  R.v41567 (state s) (inputs i) = Zmod.unsigned (N.v41567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41567 s i)) at 1.
  unfold R.v41567, N.v41567.
  unfold R.v6, N.v6.
  rewrite ?node_9201.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41568 (s : N.State) (i : N.Inputs) :
  R.v41568 (state s) (inputs i) = Zmod.unsigned (N.v41568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41568 s i)) at 1.
  unfold R.v41568, N.v41568.
  rewrite ?node_41566.
  rewrite ?node_41567.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41569 (s : N.State) (i : N.Inputs) :
  R.v41569 (state s) (inputs i) = Zmod.unsigned (N.v41569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41569 s i)) at 1.
  unfold R.v41569, N.v41569.
  rewrite ?node_41565.
  rewrite ?node_41568.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41570 (s : N.State) (i : N.Inputs) :
  R.v41570 (state s) (inputs i) = Zmod.unsigned (N.v41570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41570 s i)) at 1.
  unfold R.v41570, N.v41570.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41571 (s : N.State) (i : N.Inputs) :
  R.v41571 (state s) (inputs i) = Zmod.unsigned (N.v41571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41571 s i)) at 1.
  unfold R.v41571, N.v41571.
  rewrite ?node_9045.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41572 (s : N.State) (i : N.Inputs) :
  R.v41572 (state s) (inputs i) = Zmod.unsigned (N.v41572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41572 s i)) at 1.
  unfold R.v41572, N.v41572.
  unfold R.v6, N.v6.
  rewrite ?node_9041.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41573 (s : N.State) (i : N.Inputs) :
  R.v41573 (state s) (inputs i) = Zmod.unsigned (N.v41573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41573 s i)) at 1.
  unfold R.v41573, N.v41573.
  unfold R.v6, N.v6.
  rewrite ?node_9038.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41574 (s : N.State) (i : N.Inputs) :
  R.v41574 (state s) (inputs i) = Zmod.unsigned (N.v41574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41574 s i)) at 1.
  unfold R.v41574, N.v41574.
  rewrite ?node_41572.
  rewrite ?node_41573.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41575 (s : N.State) (i : N.Inputs) :
  R.v41575 (state s) (inputs i) = Zmod.unsigned (N.v41575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41575 s i)) at 1.
  unfold R.v41575, N.v41575.
  unfold R.v16484, N.v16484.
  rewrite ?node_41574.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41576 (s : N.State) (i : N.Inputs) :
  R.v41576 (state s) (inputs i) = Zmod.unsigned (N.v41576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41576 s i)) at 1.
  unfold R.v41576, N.v41576.
  rewrite ?node_41571.
  rewrite ?node_41575.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41577 (s : N.State) (i : N.Inputs) :
  R.v41577 (state s) (inputs i) = Zmod.unsigned (N.v41577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41577 s i)) at 1.
  unfold R.v41577, N.v41577.
  unfold R.v6, N.v6.
  rewrite ?node_41576.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41578 (s : N.State) (i : N.Inputs) :
  R.v41578 (state s) (inputs i) = Zmod.unsigned (N.v41578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41578 s i)) at 1.
  unfold R.v41578, N.v41578.
  rewrite ?node_9046.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41579 (s : N.State) (i : N.Inputs) :
  R.v41579 (state s) (inputs i) = Zmod.unsigned (N.v41579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41579 s i)) at 1.
  unfold R.v41579, N.v41579.
  unfold R.v6, N.v6.
  rewrite ?node_9205.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41580 (s : N.State) (i : N.Inputs) :
  R.v41580 (state s) (inputs i) = Zmod.unsigned (N.v41580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41580 s i)) at 1.
  unfold R.v41580, N.v41580.
  rewrite ?node_41578.
  rewrite ?node_41579.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41581 (s : N.State) (i : N.Inputs) :
  R.v41581 (state s) (inputs i) = Zmod.unsigned (N.v41581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41581 s i)) at 1.
  unfold R.v41581, N.v41581.
  rewrite ?node_41577.
  rewrite ?node_41580.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41582 (s : N.State) (i : N.Inputs) :
  R.v41582 (state s) (inputs i) = Zmod.unsigned (N.v41582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41582 s i)) at 1.
  unfold R.v41582, N.v41582.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41583 (s : N.State) (i : N.Inputs) :
  R.v41583 (state s) (inputs i) = Zmod.unsigned (N.v41583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41583 s i)) at 1.
  unfold R.v41583, N.v41583.
  rewrite ?node_9124.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41584 (s : N.State) (i : N.Inputs) :
  R.v41584 (state s) (inputs i) = Zmod.unsigned (N.v41584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41584 s i)) at 1.
  unfold R.v41584, N.v41584.
  rewrite ?node_9120.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41585 (s : N.State) (i : N.Inputs) :
  R.v41585 (state s) (inputs i) = Zmod.unsigned (N.v41585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41585 s i)) at 1.
  unfold R.v41585, N.v41585.
  rewrite ?node_9112.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41586 (s : N.State) (i : N.Inputs) :
  R.v41586 (state s) (inputs i) = Zmod.unsigned (N.v41586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41586 s i)) at 1.
  unfold R.v41586, N.v41586.
  unfold R.v6, N.v6.
  rewrite ?node_9104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41587 (s : N.State) (i : N.Inputs) :
  R.v41587 (state s) (inputs i) = Zmod.unsigned (N.v41587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41587 s i)) at 1.
  unfold R.v41587, N.v41587.
  unfold R.v6, N.v6.
  rewrite ?node_9097.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41588 (s : N.State) (i : N.Inputs) :
  R.v41588 (state s) (inputs i) = Zmod.unsigned (N.v41588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41588 s i)) at 1.
  unfold R.v41588, N.v41588.
  rewrite ?node_41586.
  rewrite ?node_41587.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41589 (s : N.State) (i : N.Inputs) :
  R.v41589 (state s) (inputs i) = Zmod.unsigned (N.v41589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41589 s i)) at 1.
  unfold R.v41589, N.v41589.
  unfold R.v16484, N.v16484.
  rewrite ?node_41588.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41590 (s : N.State) (i : N.Inputs) :
  R.v41590 (state s) (inputs i) = Zmod.unsigned (N.v41590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41590 s i)) at 1.
  unfold R.v41590, N.v41590.
  rewrite ?node_41583.
  rewrite ?node_41584.
  rewrite ?node_41585.
  rewrite ?node_41589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41591 (s : N.State) (i : N.Inputs) :
  R.v41591 (state s) (inputs i) = Zmod.unsigned (N.v41591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41591 s i)) at 1.
  unfold R.v41591, N.v41591.
  unfold R.v6, N.v6.
  rewrite ?node_41590.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41592 (s : N.State) (i : N.Inputs) :
  R.v41592 (state s) (inputs i) = Zmod.unsigned (N.v41592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41592 s i)) at 1.
  unfold R.v41592, N.v41592.
  rewrite ?node_9125.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41593 (s : N.State) (i : N.Inputs) :
  R.v41593 (state s) (inputs i) = Zmod.unsigned (N.v41593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41593 s i)) at 1.
  unfold R.v41593, N.v41593.
  unfold R.v6, N.v6.
  rewrite ?node_9264.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41594 (s : N.State) (i : N.Inputs) :
  R.v41594 (state s) (inputs i) = Zmod.unsigned (N.v41594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41594 s i)) at 1.
  unfold R.v41594, N.v41594.
  unfold R.v6, N.v6.
  rewrite ?node_9336.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41595 (s : N.State) (i : N.Inputs) :
  R.v41595 (state s) (inputs i) = Zmod.unsigned (N.v41595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41595 s i)) at 1.
  unfold R.v41595, N.v41595.
  rewrite ?node_41592.
  rewrite ?node_41593.
  rewrite ?node_41594.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41596 (s : N.State) (i : N.Inputs) :
  R.v41596 (state s) (inputs i) = Zmod.unsigned (N.v41596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41596 s i)) at 1.
  unfold R.v41596, N.v41596.
  rewrite ?node_41591.
  rewrite ?node_41595.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41597 (s : N.State) (i : N.Inputs) :
  R.v41597 (state s) (inputs i) = Zmod.unsigned (N.v41597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41597 s i)) at 1.
  unfold R.v41597, N.v41597.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41598 (s : N.State) (i : N.Inputs) :
  R.v41598 (state s) (inputs i) = Zmod.unsigned (N.v41598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41598 s i)) at 1.
  unfold R.v41598, N.v41598.
  rewrite ?node_9112.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41599 (s : N.State) (i : N.Inputs) :
  R.v41599 (state s) (inputs i) = Zmod.unsigned (N.v41599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41599 s i)) at 1.
  unfold R.v41599, N.v41599.
  unfold R.v6, N.v6.
  rewrite ?node_9104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41600 (s : N.State) (i : N.Inputs) :
  R.v41600 (state s) (inputs i) = Zmod.unsigned (N.v41600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41600 s i)) at 1.
  unfold R.v41600, N.v41600.
  unfold R.v6, N.v6.
  rewrite ?node_9097.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41601 (s : N.State) (i : N.Inputs) :
  R.v41601 (state s) (inputs i) = Zmod.unsigned (N.v41601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41601 s i)) at 1.
  unfold R.v41601, N.v41601.
  rewrite ?node_41599.
  rewrite ?node_41600.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41602 (s : N.State) (i : N.Inputs) :
  R.v41602 (state s) (inputs i) = Zmod.unsigned (N.v41602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41602 s i)) at 1.
  unfold R.v41602, N.v41602.
  unfold R.v16484, N.v16484.
  rewrite ?node_41601.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41603 (s : N.State) (i : N.Inputs) :
  R.v41603 (state s) (inputs i) = Zmod.unsigned (N.v41603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41603 s i)) at 1.
  unfold R.v41603, N.v41603.
  rewrite ?node_41598.
  rewrite ?node_41602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41604 (s : N.State) (i : N.Inputs) :
  R.v41604 (state s) (inputs i) = Zmod.unsigned (N.v41604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41604 s i)) at 1.
  unfold R.v41604, N.v41604.
  unfold R.v6, N.v6.
  rewrite ?node_41603.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41605 (s : N.State) (i : N.Inputs) :
  R.v41605 (state s) (inputs i) = Zmod.unsigned (N.v41605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41605 s i)) at 1.
  unfold R.v41605, N.v41605.
  rewrite ?node_9113.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41606 (s : N.State) (i : N.Inputs) :
  R.v41606 (state s) (inputs i) = Zmod.unsigned (N.v41606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41606 s i)) at 1.
  unfold R.v41606, N.v41606.
  unfold R.v6, N.v6.
  rewrite ?node_9264.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41607 (s : N.State) (i : N.Inputs) :
  R.v41607 (state s) (inputs i) = Zmod.unsigned (N.v41607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41607 s i)) at 1.
  unfold R.v41607, N.v41607.
  rewrite ?node_41605.
  rewrite ?node_41606.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41608 (s : N.State) (i : N.Inputs) :
  R.v41608 (state s) (inputs i) = Zmod.unsigned (N.v41608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41608 s i)) at 1.
  unfold R.v41608, N.v41608.
  rewrite ?node_41604.
  rewrite ?node_41607.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41609 (s : N.State) (i : N.Inputs) :
  R.v41609 (state s) (inputs i) = Zmod.unsigned (N.v41609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41609 s i)) at 1.
  unfold R.v41609, N.v41609.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41610 (s : N.State) (i : N.Inputs) :
  R.v41610 (state s) (inputs i) = Zmod.unsigned (N.v41610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41610 s i)) at 1.
  unfold R.v41610, N.v41610.
  rewrite ?node_9124.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41611 (s : N.State) (i : N.Inputs) :
  R.v41611 (state s) (inputs i) = Zmod.unsigned (N.v41611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41611 s i)) at 1.
  unfold R.v41611, N.v41611.
  unfold R.v6, N.v6.
  rewrite ?node_9120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41612 (s : N.State) (i : N.Inputs) :
  R.v41612 (state s) (inputs i) = Zmod.unsigned (N.v41612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41612 s i)) at 1.
  unfold R.v41612, N.v41612.
  unfold R.v6, N.v6.
  rewrite ?node_9113.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41613 (s : N.State) (i : N.Inputs) :
  R.v41613 (state s) (inputs i) = Zmod.unsigned (N.v41613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41613 s i)) at 1.
  unfold R.v41613, N.v41613.
  rewrite ?node_41611.
  rewrite ?node_41612.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41614 (s : N.State) (i : N.Inputs) :
  R.v41614 (state s) (inputs i) = Zmod.unsigned (N.v41614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41614 s i)) at 1.
  unfold R.v41614, N.v41614.
  unfold R.v16484, N.v16484.
  rewrite ?node_41613.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41615 (s : N.State) (i : N.Inputs) :
  R.v41615 (state s) (inputs i) = Zmod.unsigned (N.v41615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41615 s i)) at 1.
  unfold R.v41615, N.v41615.
  rewrite ?node_41610.
  rewrite ?node_41614.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41616 (s : N.State) (i : N.Inputs) :
  R.v41616 (state s) (inputs i) = Zmod.unsigned (N.v41616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41616 s i)) at 1.
  unfold R.v41616, N.v41616.
  unfold R.v6, N.v6.
  rewrite ?node_41615.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41617 (s : N.State) (i : N.Inputs) :
  R.v41617 (state s) (inputs i) = Zmod.unsigned (N.v41617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41617 s i)) at 1.
  unfold R.v41617, N.v41617.
  rewrite ?node_9125.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41618 (s : N.State) (i : N.Inputs) :
  R.v41618 (state s) (inputs i) = Zmod.unsigned (N.v41618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41618 s i)) at 1.
  unfold R.v41618, N.v41618.
  unfold R.v6, N.v6.
  rewrite ?node_9336.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41619 (s : N.State) (i : N.Inputs) :
  R.v41619 (state s) (inputs i) = Zmod.unsigned (N.v41619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41619 s i)) at 1.
  unfold R.v41619, N.v41619.
  rewrite ?node_41617.
  rewrite ?node_41618.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41620 (s : N.State) (i : N.Inputs) :
  R.v41620 (state s) (inputs i) = Zmod.unsigned (N.v41620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41620 s i)) at 1.
  unfold R.v41620, N.v41620.
  rewrite ?node_41616.
  rewrite ?node_41619.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41621 (s : N.State) (i : N.Inputs) :
  R.v41621 (state s) (inputs i) = Zmod.unsigned (N.v41621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41621 s i)) at 1.
  unfold R.v41621, N.v41621.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41622 (s : N.State) (i : N.Inputs) :
  R.v41622 (state s) (inputs i) = Zmod.unsigned (N.v41622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41622 s i)) at 1.
  unfold R.v41622, N.v41622.
  rewrite ?node_9153.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41623 (s : N.State) (i : N.Inputs) :
  R.v41623 (state s) (inputs i) = Zmod.unsigned (N.v41623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41623 s i)) at 1.
  unfold R.v41623, N.v41623.
  rewrite ?node_9149.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41624 (s : N.State) (i : N.Inputs) :
  R.v41624 (state s) (inputs i) = Zmod.unsigned (N.v41624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41624 s i)) at 1.
  unfold R.v41624, N.v41624.
  rewrite ?node_9147.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41625 (s : N.State) (i : N.Inputs) :
  R.v41625 (state s) (inputs i) = Zmod.unsigned (N.v41625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41625 s i)) at 1.
  unfold R.v41625, N.v41625.
  unfold R.v6, N.v6.
  rewrite ?node_9139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41626 (s : N.State) (i : N.Inputs) :
  R.v41626 (state s) (inputs i) = Zmod.unsigned (N.v41626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41626 s i)) at 1.
  unfold R.v41626, N.v41626.
  unfold R.v6, N.v6.
  rewrite ?node_9132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41627 (s : N.State) (i : N.Inputs) :
  R.v41627 (state s) (inputs i) = Zmod.unsigned (N.v41627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41627 s i)) at 1.
  unfold R.v41627, N.v41627.
  rewrite ?node_41625.
  rewrite ?node_41626.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41628 (s : N.State) (i : N.Inputs) :
  R.v41628 (state s) (inputs i) = Zmod.unsigned (N.v41628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41628 s i)) at 1.
  unfold R.v41628, N.v41628.
  unfold R.v16484, N.v16484.
  rewrite ?node_41627.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41629 (s : N.State) (i : N.Inputs) :
  R.v41629 (state s) (inputs i) = Zmod.unsigned (N.v41629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41629 s i)) at 1.
  unfold R.v41629, N.v41629.
  rewrite ?node_41622.
  rewrite ?node_41623.
  rewrite ?node_41624.
  rewrite ?node_41628.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41630 (s : N.State) (i : N.Inputs) :
  R.v41630 (state s) (inputs i) = Zmod.unsigned (N.v41630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41630 s i)) at 1.
  unfold R.v41630, N.v41630.
  unfold R.v6, N.v6.
  rewrite ?node_41629.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41631 (s : N.State) (i : N.Inputs) :
  R.v41631 (state s) (inputs i) = Zmod.unsigned (N.v41631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41631 s i)) at 1.
  unfold R.v41631, N.v41631.
  rewrite ?node_9154.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41632 (s : N.State) (i : N.Inputs) :
  R.v41632 (state s) (inputs i) = Zmod.unsigned (N.v41632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41632 s i)) at 1.
  unfold R.v41632, N.v41632.
  unfold R.v6, N.v6.
  rewrite ?node_9293.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41633 (s : N.State) (i : N.Inputs) :
  R.v41633 (state s) (inputs i) = Zmod.unsigned (N.v41633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41633 s i)) at 1.
  unfold R.v41633, N.v41633.
  unfold R.v6, N.v6.
  rewrite ?node_9339.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41634 (s : N.State) (i : N.Inputs) :
  R.v41634 (state s) (inputs i) = Zmod.unsigned (N.v41634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41634 s i)) at 1.
  unfold R.v41634, N.v41634.
  rewrite ?node_41631.
  rewrite ?node_41632.
  rewrite ?node_41633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41635 (s : N.State) (i : N.Inputs) :
  R.v41635 (state s) (inputs i) = Zmod.unsigned (N.v41635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41635 s i)) at 1.
  unfold R.v41635, N.v41635.
  rewrite ?node_41630.
  rewrite ?node_41634.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41636 (s : N.State) (i : N.Inputs) :
  R.v41636 (state s) (inputs i) = Zmod.unsigned (N.v41636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41636 s i)) at 1.
  unfold R.v41636, N.v41636.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41637 (s : N.State) (i : N.Inputs) :
  R.v41637 (state s) (inputs i) = Zmod.unsigned (N.v41637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41637 s i)) at 1.
  unfold R.v41637, N.v41637.
  rewrite ?node_9147.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41638 (s : N.State) (i : N.Inputs) :
  R.v41638 (state s) (inputs i) = Zmod.unsigned (N.v41638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41638 s i)) at 1.
  unfold R.v41638, N.v41638.
  unfold R.v6, N.v6.
  rewrite ?node_9139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41639 (s : N.State) (i : N.Inputs) :
  R.v41639 (state s) (inputs i) = Zmod.unsigned (N.v41639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41639 s i)) at 1.
  unfold R.v41639, N.v41639.
  unfold R.v6, N.v6.
  rewrite ?node_9132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41640 (s : N.State) (i : N.Inputs) :
  R.v41640 (state s) (inputs i) = Zmod.unsigned (N.v41640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41640 s i)) at 1.
  unfold R.v41640, N.v41640.
  rewrite ?node_41638.
  rewrite ?node_41639.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41641 (s : N.State) (i : N.Inputs) :
  R.v41641 (state s) (inputs i) = Zmod.unsigned (N.v41641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41641 s i)) at 1.
  unfold R.v41641, N.v41641.
  unfold R.v16484, N.v16484.
  rewrite ?node_41640.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41642 (s : N.State) (i : N.Inputs) :
  R.v41642 (state s) (inputs i) = Zmod.unsigned (N.v41642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41642 s i)) at 1.
  unfold R.v41642, N.v41642.
  rewrite ?node_41637.
  rewrite ?node_41641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41643 (s : N.State) (i : N.Inputs) :
  R.v41643 (state s) (inputs i) = Zmod.unsigned (N.v41643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41643 s i)) at 1.
  unfold R.v41643, N.v41643.
  unfold R.v6, N.v6.
  rewrite ?node_41642.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41644 (s : N.State) (i : N.Inputs) :
  R.v41644 (state s) (inputs i) = Zmod.unsigned (N.v41644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41644 s i)) at 1.
  unfold R.v41644, N.v41644.
  rewrite ?node_9148.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41645 (s : N.State) (i : N.Inputs) :
  R.v41645 (state s) (inputs i) = Zmod.unsigned (N.v41645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41645 s i)) at 1.
  unfold R.v41645, N.v41645.
  unfold R.v6, N.v6.
  rewrite ?node_9293.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41646 (s : N.State) (i : N.Inputs) :
  R.v41646 (state s) (inputs i) = Zmod.unsigned (N.v41646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41646 s i)) at 1.
  unfold R.v41646, N.v41646.
  rewrite ?node_41644.
  rewrite ?node_41645.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41647 (s : N.State) (i : N.Inputs) :
  R.v41647 (state s) (inputs i) = Zmod.unsigned (N.v41647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41647 s i)) at 1.
  unfold R.v41647, N.v41647.
  rewrite ?node_41643.
  rewrite ?node_41646.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41648 (s : N.State) (i : N.Inputs) :
  R.v41648 (state s) (inputs i) = Zmod.unsigned (N.v41648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41648 s i)) at 1.
  unfold R.v41648, N.v41648.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41649 (s : N.State) (i : N.Inputs) :
  R.v41649 (state s) (inputs i) = Zmod.unsigned (N.v41649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41649 s i)) at 1.
  unfold R.v41649, N.v41649.
  rewrite ?node_9153.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41650 (s : N.State) (i : N.Inputs) :
  R.v41650 (state s) (inputs i) = Zmod.unsigned (N.v41650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41650 s i)) at 1.
  unfold R.v41650, N.v41650.
  unfold R.v6, N.v6.
  rewrite ?node_9149.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41651 (s : N.State) (i : N.Inputs) :
  R.v41651 (state s) (inputs i) = Zmod.unsigned (N.v41651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41651 s i)) at 1.
  unfold R.v41651, N.v41651.
  unfold R.v6, N.v6.
  rewrite ?node_9148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41652 (s : N.State) (i : N.Inputs) :
  R.v41652 (state s) (inputs i) = Zmod.unsigned (N.v41652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41652 s i)) at 1.
  unfold R.v41652, N.v41652.
  rewrite ?node_41650.
  rewrite ?node_41651.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41653 (s : N.State) (i : N.Inputs) :
  R.v41653 (state s) (inputs i) = Zmod.unsigned (N.v41653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41653 s i)) at 1.
  unfold R.v41653, N.v41653.
  unfold R.v16484, N.v16484.
  rewrite ?node_41652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41654 (s : N.State) (i : N.Inputs) :
  R.v41654 (state s) (inputs i) = Zmod.unsigned (N.v41654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41654 s i)) at 1.
  unfold R.v41654, N.v41654.
  rewrite ?node_41649.
  rewrite ?node_41653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41655 (s : N.State) (i : N.Inputs) :
  R.v41655 (state s) (inputs i) = Zmod.unsigned (N.v41655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41655 s i)) at 1.
  unfold R.v41655, N.v41655.
  unfold R.v6, N.v6.
  rewrite ?node_41654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41656 (s : N.State) (i : N.Inputs) :
  R.v41656 (state s) (inputs i) = Zmod.unsigned (N.v41656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41656 s i)) at 1.
  unfold R.v41656, N.v41656.
  rewrite ?node_9154.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41657 (s : N.State) (i : N.Inputs) :
  R.v41657 (state s) (inputs i) = Zmod.unsigned (N.v41657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41657 s i)) at 1.
  unfold R.v41657, N.v41657.
  unfold R.v6, N.v6.
  rewrite ?node_9339.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41658 (s : N.State) (i : N.Inputs) :
  R.v41658 (state s) (inputs i) = Zmod.unsigned (N.v41658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41658 s i)) at 1.
  unfold R.v41658, N.v41658.
  rewrite ?node_41656.
  rewrite ?node_41657.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41659 (s : N.State) (i : N.Inputs) :
  R.v41659 (state s) (inputs i) = Zmod.unsigned (N.v41659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41659 s i)) at 1.
  unfold R.v41659, N.v41659.
  rewrite ?node_41655.
  rewrite ?node_41658.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41660 (s : N.State) (i : N.Inputs) :
  R.v41660 (state s) (inputs i) = Zmod.unsigned (N.v41660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41660 s i)) at 1.
  unfold R.v41660, N.v41660.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41661 (s : N.State) (i : N.Inputs) :
  R.v41661 (state s) (inputs i) = Zmod.unsigned (N.v41661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41661 s i)) at 1.
  unfold R.v41661, N.v41661.
  rewrite ?node_9173.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41662 (s : N.State) (i : N.Inputs) :
  R.v41662 (state s) (inputs i) = Zmod.unsigned (N.v41662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41662 s i)) at 1.
  unfold R.v41662, N.v41662.
  rewrite ?node_9169.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41663 (s : N.State) (i : N.Inputs) :
  R.v41663 (state s) (inputs i) = Zmod.unsigned (N.v41663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41663 s i)) at 1.
  unfold R.v41663, N.v41663.
  rewrite ?node_9165.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41664 (s : N.State) (i : N.Inputs) :
  R.v41664 (state s) (inputs i) = Zmod.unsigned (N.v41664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41664 s i)) at 1.
  unfold R.v41664, N.v41664.
  unfold R.v6, N.v6.
  rewrite ?node_9161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41665 (s : N.State) (i : N.Inputs) :
  R.v41665 (state s) (inputs i) = Zmod.unsigned (N.v41665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41665 s i)) at 1.
  unfold R.v41665, N.v41665.
  unfold R.v6, N.v6.
  rewrite ?node_9158.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41666 (s : N.State) (i : N.Inputs) :
  R.v41666 (state s) (inputs i) = Zmod.unsigned (N.v41666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41666 s i)) at 1.
  unfold R.v41666, N.v41666.
  rewrite ?node_41664.
  rewrite ?node_41665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41667 (s : N.State) (i : N.Inputs) :
  R.v41667 (state s) (inputs i) = Zmod.unsigned (N.v41667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41667 s i)) at 1.
  unfold R.v41667, N.v41667.
  unfold R.v16484, N.v16484.
  rewrite ?node_41666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41668 (s : N.State) (i : N.Inputs) :
  R.v41668 (state s) (inputs i) = Zmod.unsigned (N.v41668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41668 s i)) at 1.
  unfold R.v41668, N.v41668.
  rewrite ?node_41661.
  rewrite ?node_41662.
  rewrite ?node_41663.
  rewrite ?node_41667.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41669 (s : N.State) (i : N.Inputs) :
  R.v41669 (state s) (inputs i) = Zmod.unsigned (N.v41669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41669 s i)) at 1.
  unfold R.v41669, N.v41669.
  unfold R.v6, N.v6.
  rewrite ?node_41668.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41670 (s : N.State) (i : N.Inputs) :
  R.v41670 (state s) (inputs i) = Zmod.unsigned (N.v41670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41670 s i)) at 1.
  unfold R.v41670, N.v41670.
  rewrite ?node_9174.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41671 (s : N.State) (i : N.Inputs) :
  R.v41671 (state s) (inputs i) = Zmod.unsigned (N.v41671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41671 s i)) at 1.
  unfold R.v41671, N.v41671.
  unfold R.v6, N.v6.
  rewrite ?node_9313.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41672 (s : N.State) (i : N.Inputs) :
  R.v41672 (state s) (inputs i) = Zmod.unsigned (N.v41672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41672 s i)) at 1.
  unfold R.v41672, N.v41672.
  unfold R.v6, N.v6.
  rewrite ?node_9343.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41673 (s : N.State) (i : N.Inputs) :
  R.v41673 (state s) (inputs i) = Zmod.unsigned (N.v41673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41673 s i)) at 1.
  unfold R.v41673, N.v41673.
  rewrite ?node_41670.
  rewrite ?node_41671.
  rewrite ?node_41672.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41674 (s : N.State) (i : N.Inputs) :
  R.v41674 (state s) (inputs i) = Zmod.unsigned (N.v41674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41674 s i)) at 1.
  unfold R.v41674, N.v41674.
  rewrite ?node_41669.
  rewrite ?node_41673.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41675 (s : N.State) (i : N.Inputs) :
  R.v41675 (state s) (inputs i) = Zmod.unsigned (N.v41675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41675 s i)) at 1.
  unfold R.v41675, N.v41675.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41676 (s : N.State) (i : N.Inputs) :
  R.v41676 (state s) (inputs i) = Zmod.unsigned (N.v41676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41676 s i)) at 1.
  unfold R.v41676, N.v41676.
  rewrite ?node_9165.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41677 (s : N.State) (i : N.Inputs) :
  R.v41677 (state s) (inputs i) = Zmod.unsigned (N.v41677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41677 s i)) at 1.
  unfold R.v41677, N.v41677.
  unfold R.v6, N.v6.
  rewrite ?node_9161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41678 (s : N.State) (i : N.Inputs) :
  R.v41678 (state s) (inputs i) = Zmod.unsigned (N.v41678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41678 s i)) at 1.
  unfold R.v41678, N.v41678.
  unfold R.v6, N.v6.
  rewrite ?node_9158.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41679 (s : N.State) (i : N.Inputs) :
  R.v41679 (state s) (inputs i) = Zmod.unsigned (N.v41679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41679 s i)) at 1.
  unfold R.v41679, N.v41679.
  rewrite ?node_41677.
  rewrite ?node_41678.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41680 (s : N.State) (i : N.Inputs) :
  R.v41680 (state s) (inputs i) = Zmod.unsigned (N.v41680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41680 s i)) at 1.
  unfold R.v41680, N.v41680.
  unfold R.v16484, N.v16484.
  rewrite ?node_41679.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41681 (s : N.State) (i : N.Inputs) :
  R.v41681 (state s) (inputs i) = Zmod.unsigned (N.v41681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41681 s i)) at 1.
  unfold R.v41681, N.v41681.
  rewrite ?node_41676.
  rewrite ?node_41680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41682 (s : N.State) (i : N.Inputs) :
  R.v41682 (state s) (inputs i) = Zmod.unsigned (N.v41682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41682 s i)) at 1.
  unfold R.v41682, N.v41682.
  unfold R.v6, N.v6.
  rewrite ?node_41681.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41683 (s : N.State) (i : N.Inputs) :
  R.v41683 (state s) (inputs i) = Zmod.unsigned (N.v41683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41683 s i)) at 1.
  unfold R.v41683, N.v41683.
  rewrite ?node_9166.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41684 (s : N.State) (i : N.Inputs) :
  R.v41684 (state s) (inputs i) = Zmod.unsigned (N.v41684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41684 s i)) at 1.
  unfold R.v41684, N.v41684.
  unfold R.v6, N.v6.
  rewrite ?node_9313.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41685 (s : N.State) (i : N.Inputs) :
  R.v41685 (state s) (inputs i) = Zmod.unsigned (N.v41685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41685 s i)) at 1.
  unfold R.v41685, N.v41685.
  rewrite ?node_41683.
  rewrite ?node_41684.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41686 (s : N.State) (i : N.Inputs) :
  R.v41686 (state s) (inputs i) = Zmod.unsigned (N.v41686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41686 s i)) at 1.
  unfold R.v41686, N.v41686.
  rewrite ?node_41682.
  rewrite ?node_41685.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41687 (s : N.State) (i : N.Inputs) :
  R.v41687 (state s) (inputs i) = Zmod.unsigned (N.v41687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41687 s i)) at 1.
  unfold R.v41687, N.v41687.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41688 (s : N.State) (i : N.Inputs) :
  R.v41688 (state s) (inputs i) = Zmod.unsigned (N.v41688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41688 s i)) at 1.
  unfold R.v41688, N.v41688.
  rewrite ?node_9173.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41689 (s : N.State) (i : N.Inputs) :
  R.v41689 (state s) (inputs i) = Zmod.unsigned (N.v41689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41689 s i)) at 1.
  unfold R.v41689, N.v41689.
  unfold R.v6, N.v6.
  rewrite ?node_9169.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41690 (s : N.State) (i : N.Inputs) :
  R.v41690 (state s) (inputs i) = Zmod.unsigned (N.v41690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41690 s i)) at 1.
  unfold R.v41690, N.v41690.
  unfold R.v6, N.v6.
  rewrite ?node_9166.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41691 (s : N.State) (i : N.Inputs) :
  R.v41691 (state s) (inputs i) = Zmod.unsigned (N.v41691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41691 s i)) at 1.
  unfold R.v41691, N.v41691.
  rewrite ?node_41689.
  rewrite ?node_41690.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41692 (s : N.State) (i : N.Inputs) :
  R.v41692 (state s) (inputs i) = Zmod.unsigned (N.v41692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41692 s i)) at 1.
  unfold R.v41692, N.v41692.
  unfold R.v16484, N.v16484.
  rewrite ?node_41691.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41693 (s : N.State) (i : N.Inputs) :
  R.v41693 (state s) (inputs i) = Zmod.unsigned (N.v41693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41693 s i)) at 1.
  unfold R.v41693, N.v41693.
  rewrite ?node_41688.
  rewrite ?node_41692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41694 (s : N.State) (i : N.Inputs) :
  R.v41694 (state s) (inputs i) = Zmod.unsigned (N.v41694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41694 s i)) at 1.
  unfold R.v41694, N.v41694.
  unfold R.v6, N.v6.
  rewrite ?node_41693.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41695 (s : N.State) (i : N.Inputs) :
  R.v41695 (state s) (inputs i) = Zmod.unsigned (N.v41695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41695 s i)) at 1.
  unfold R.v41695, N.v41695.
  rewrite ?node_9174.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41696 (s : N.State) (i : N.Inputs) :
  R.v41696 (state s) (inputs i) = Zmod.unsigned (N.v41696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41696 s i)) at 1.
  unfold R.v41696, N.v41696.
  unfold R.v6, N.v6.
  rewrite ?node_9343.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41697 (s : N.State) (i : N.Inputs) :
  R.v41697 (state s) (inputs i) = Zmod.unsigned (N.v41697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41697 s i)) at 1.
  unfold R.v41697, N.v41697.
  rewrite ?node_41695.
  rewrite ?node_41696.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41698 (s : N.State) (i : N.Inputs) :
  R.v41698 (state s) (inputs i) = Zmod.unsigned (N.v41698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41698 s i)) at 1.
  unfold R.v41698, N.v41698.
  rewrite ?node_41694.
  rewrite ?node_41697.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41699 (s : N.State) (i : N.Inputs) :
  R.v41699 (state s) (inputs i) = Zmod.unsigned (N.v41699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41699 s i)) at 1.
  unfold R.v41699, N.v41699.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41700 (s : N.State) (i : N.Inputs) :
  R.v41700 (state s) (inputs i) = Zmod.unsigned (N.v41700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41700 s i)) at 1.
  unfold R.v41700, N.v41700.
  rewrite ?node_9185.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41701 (s : N.State) (i : N.Inputs) :
  R.v41701 (state s) (inputs i) = Zmod.unsigned (N.v41701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41701 s i)) at 1.
  unfold R.v41701, N.v41701.
  unfold R.v6, N.v6.
  rewrite ?node_9181.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41702 (s : N.State) (i : N.Inputs) :
  R.v41702 (state s) (inputs i) = Zmod.unsigned (N.v41702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41702 s i)) at 1.
  unfold R.v41702, N.v41702.
  unfold R.v6, N.v6.
  rewrite ?node_9178.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41703 (s : N.State) (i : N.Inputs) :
  R.v41703 (state s) (inputs i) = Zmod.unsigned (N.v41703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41703 s i)) at 1.
  unfold R.v41703, N.v41703.
  rewrite ?node_41701.
  rewrite ?node_41702.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41704 (s : N.State) (i : N.Inputs) :
  R.v41704 (state s) (inputs i) = Zmod.unsigned (N.v41704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41704 s i)) at 1.
  unfold R.v41704, N.v41704.
  unfold R.v16484, N.v16484.
  rewrite ?node_41703.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41705 (s : N.State) (i : N.Inputs) :
  R.v41705 (state s) (inputs i) = Zmod.unsigned (N.v41705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41705 s i)) at 1.
  unfold R.v41705, N.v41705.
  rewrite ?node_41700.
  rewrite ?node_41704.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41706 (s : N.State) (i : N.Inputs) :
  R.v41706 (state s) (inputs i) = Zmod.unsigned (N.v41706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41706 s i)) at 1.
  unfold R.v41706, N.v41706.
  unfold R.v6, N.v6.
  rewrite ?node_41705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41707 (s : N.State) (i : N.Inputs) :
  R.v41707 (state s) (inputs i) = Zmod.unsigned (N.v41707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41707 s i)) at 1.
  unfold R.v41707, N.v41707.
  rewrite ?node_9186.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41708 (s : N.State) (i : N.Inputs) :
  R.v41708 (state s) (inputs i) = Zmod.unsigned (N.v41708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41708 s i)) at 1.
  unfold R.v41708, N.v41708.
  unfold R.v6, N.v6.
  rewrite ?node_9347.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41709 (s : N.State) (i : N.Inputs) :
  R.v41709 (state s) (inputs i) = Zmod.unsigned (N.v41709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41709 s i)) at 1.
  unfold R.v41709, N.v41709.
  rewrite ?node_41707.
  rewrite ?node_41708.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41710 (s : N.State) (i : N.Inputs) :
  R.v41710 (state s) (inputs i) = Zmod.unsigned (N.v41710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41710 s i)) at 1.
  unfold R.v41710, N.v41710.
  rewrite ?node_41706.
  rewrite ?node_41709.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41711 (s : N.State) (i : N.Inputs) :
  R.v41711 (state s) (inputs i) = Zmod.unsigned (N.v41711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41711 s i)) at 1.
  unfold R.v41711, N.v41711.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41712 (s : N.State) (i : N.Inputs) :
  R.v41712 (state s) (inputs i) = Zmod.unsigned (N.v41712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41712 s i)) at 1.
  unfold R.v41712, N.v41712.
  rewrite ?node_9264.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41713 (s : N.State) (i : N.Inputs) :
  R.v41713 (state s) (inputs i) = Zmod.unsigned (N.v41713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41713 s i)) at 1.
  unfold R.v41713, N.v41713.
  rewrite ?node_9260.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41714 (s : N.State) (i : N.Inputs) :
  R.v41714 (state s) (inputs i) = Zmod.unsigned (N.v41714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41714 s i)) at 1.
  unfold R.v41714, N.v41714.
  rewrite ?node_9252.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41715 (s : N.State) (i : N.Inputs) :
  R.v41715 (state s) (inputs i) = Zmod.unsigned (N.v41715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41715 s i)) at 1.
  unfold R.v41715, N.v41715.
  unfold R.v6, N.v6.
  rewrite ?node_9244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41716 (s : N.State) (i : N.Inputs) :
  R.v41716 (state s) (inputs i) = Zmod.unsigned (N.v41716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41716 s i)) at 1.
  unfold R.v41716, N.v41716.
  unfold R.v6, N.v6.
  rewrite ?node_9237.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41717 (s : N.State) (i : N.Inputs) :
  R.v41717 (state s) (inputs i) = Zmod.unsigned (N.v41717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41717 s i)) at 1.
  unfold R.v41717, N.v41717.
  rewrite ?node_41715.
  rewrite ?node_41716.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41718 (s : N.State) (i : N.Inputs) :
  R.v41718 (state s) (inputs i) = Zmod.unsigned (N.v41718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41718 s i)) at 1.
  unfold R.v41718, N.v41718.
  unfold R.v16484, N.v16484.
  rewrite ?node_41717.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41719 (s : N.State) (i : N.Inputs) :
  R.v41719 (state s) (inputs i) = Zmod.unsigned (N.v41719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41719 s i)) at 1.
  unfold R.v41719, N.v41719.
  rewrite ?node_41712.
  rewrite ?node_41713.
  rewrite ?node_41714.
  rewrite ?node_41718.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41720 (s : N.State) (i : N.Inputs) :
  R.v41720 (state s) (inputs i) = Zmod.unsigned (N.v41720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41720 s i)) at 1.
  unfold R.v41720, N.v41720.
  unfold R.v6, N.v6.
  rewrite ?node_41719.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41721 (s : N.State) (i : N.Inputs) :
  R.v41721 (state s) (inputs i) = Zmod.unsigned (N.v41721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41721 s i)) at 1.
  unfold R.v41721, N.v41721.
  rewrite ?node_9265.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41722 (s : N.State) (i : N.Inputs) :
  R.v41722 (state s) (inputs i) = Zmod.unsigned (N.v41722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41722 s i)) at 1.
  unfold R.v41722, N.v41722.
  unfold R.v6, N.v6.
  rewrite ?node_9406.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41723 (s : N.State) (i : N.Inputs) :
  R.v41723 (state s) (inputs i) = Zmod.unsigned (N.v41723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41723 s i)) at 1.
  unfold R.v41723, N.v41723.
  unfold R.v6, N.v6.
  rewrite ?node_9483.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41724 (s : N.State) (i : N.Inputs) :
  R.v41724 (state s) (inputs i) = Zmod.unsigned (N.v41724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41724 s i)) at 1.
  unfold R.v41724, N.v41724.
  rewrite ?node_41721.
  rewrite ?node_41722.
  rewrite ?node_41723.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41725 (s : N.State) (i : N.Inputs) :
  R.v41725 (state s) (inputs i) = Zmod.unsigned (N.v41725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41725 s i)) at 1.
  unfold R.v41725, N.v41725.
  rewrite ?node_41720.
  rewrite ?node_41724.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41726 (s : N.State) (i : N.Inputs) :
  R.v41726 (state s) (inputs i) = Zmod.unsigned (N.v41726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41726 s i)) at 1.
  unfold R.v41726, N.v41726.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41727 (s : N.State) (i : N.Inputs) :
  R.v41727 (state s) (inputs i) = Zmod.unsigned (N.v41727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41727 s i)) at 1.
  unfold R.v41727, N.v41727.
  rewrite ?node_9252.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41728 (s : N.State) (i : N.Inputs) :
  R.v41728 (state s) (inputs i) = Zmod.unsigned (N.v41728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41728 s i)) at 1.
  unfold R.v41728, N.v41728.
  unfold R.v6, N.v6.
  rewrite ?node_9244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41729 (s : N.State) (i : N.Inputs) :
  R.v41729 (state s) (inputs i) = Zmod.unsigned (N.v41729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41729 s i)) at 1.
  unfold R.v41729, N.v41729.
  unfold R.v6, N.v6.
  rewrite ?node_9237.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41730 (s : N.State) (i : N.Inputs) :
  R.v41730 (state s) (inputs i) = Zmod.unsigned (N.v41730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41730 s i)) at 1.
  unfold R.v41730, N.v41730.
  rewrite ?node_41728.
  rewrite ?node_41729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41731 (s : N.State) (i : N.Inputs) :
  R.v41731 (state s) (inputs i) = Zmod.unsigned (N.v41731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41731 s i)) at 1.
  unfold R.v41731, N.v41731.
  unfold R.v16484, N.v16484.
  rewrite ?node_41730.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41732 (s : N.State) (i : N.Inputs) :
  R.v41732 (state s) (inputs i) = Zmod.unsigned (N.v41732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41732 s i)) at 1.
  unfold R.v41732, N.v41732.
  rewrite ?node_41727.
  rewrite ?node_41731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41733 (s : N.State) (i : N.Inputs) :
  R.v41733 (state s) (inputs i) = Zmod.unsigned (N.v41733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41733 s i)) at 1.
  unfold R.v41733, N.v41733.
  unfold R.v6, N.v6.
  rewrite ?node_41732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41734 (s : N.State) (i : N.Inputs) :
  R.v41734 (state s) (inputs i) = Zmod.unsigned (N.v41734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41734 s i)) at 1.
  unfold R.v41734, N.v41734.
  rewrite ?node_9253.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41735 (s : N.State) (i : N.Inputs) :
  R.v41735 (state s) (inputs i) = Zmod.unsigned (N.v41735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41735 s i)) at 1.
  unfold R.v41735, N.v41735.
  unfold R.v6, N.v6.
  rewrite ?node_9406.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41736 (s : N.State) (i : N.Inputs) :
  R.v41736 (state s) (inputs i) = Zmod.unsigned (N.v41736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41736 s i)) at 1.
  unfold R.v41736, N.v41736.
  rewrite ?node_41734.
  rewrite ?node_41735.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41737 (s : N.State) (i : N.Inputs) :
  R.v41737 (state s) (inputs i) = Zmod.unsigned (N.v41737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41737 s i)) at 1.
  unfold R.v41737, N.v41737.
  rewrite ?node_41733.
  rewrite ?node_41736.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41738 (s : N.State) (i : N.Inputs) :
  R.v41738 (state s) (inputs i) = Zmod.unsigned (N.v41738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41738 s i)) at 1.
  unfold R.v41738, N.v41738.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41739 (s : N.State) (i : N.Inputs) :
  R.v41739 (state s) (inputs i) = Zmod.unsigned (N.v41739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41739 s i)) at 1.
  unfold R.v41739, N.v41739.
  rewrite ?node_9264.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41740 (s : N.State) (i : N.Inputs) :
  R.v41740 (state s) (inputs i) = Zmod.unsigned (N.v41740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41740 s i)) at 1.
  unfold R.v41740, N.v41740.
  unfold R.v6, N.v6.
  rewrite ?node_9260.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41741 (s : N.State) (i : N.Inputs) :
  R.v41741 (state s) (inputs i) = Zmod.unsigned (N.v41741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41741 s i)) at 1.
  unfold R.v41741, N.v41741.
  unfold R.v6, N.v6.
  rewrite ?node_9253.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41742 (s : N.State) (i : N.Inputs) :
  R.v41742 (state s) (inputs i) = Zmod.unsigned (N.v41742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41742 s i)) at 1.
  unfold R.v41742, N.v41742.
  rewrite ?node_41740.
  rewrite ?node_41741.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41743 (s : N.State) (i : N.Inputs) :
  R.v41743 (state s) (inputs i) = Zmod.unsigned (N.v41743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41743 s i)) at 1.
  unfold R.v41743, N.v41743.
  unfold R.v16484, N.v16484.
  rewrite ?node_41742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41744 (s : N.State) (i : N.Inputs) :
  R.v41744 (state s) (inputs i) = Zmod.unsigned (N.v41744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41744 s i)) at 1.
  unfold R.v41744, N.v41744.
  rewrite ?node_41739.
  rewrite ?node_41743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41745 (s : N.State) (i : N.Inputs) :
  R.v41745 (state s) (inputs i) = Zmod.unsigned (N.v41745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41745 s i)) at 1.
  unfold R.v41745, N.v41745.
  unfold R.v6, N.v6.
  rewrite ?node_41744.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41746 (s : N.State) (i : N.Inputs) :
  R.v41746 (state s) (inputs i) = Zmod.unsigned (N.v41746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41746 s i)) at 1.
  unfold R.v41746, N.v41746.
  rewrite ?node_9265.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41747 (s : N.State) (i : N.Inputs) :
  R.v41747 (state s) (inputs i) = Zmod.unsigned (N.v41747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41747 s i)) at 1.
  unfold R.v41747, N.v41747.
  unfold R.v6, N.v6.
  rewrite ?node_9483.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41748 (s : N.State) (i : N.Inputs) :
  R.v41748 (state s) (inputs i) = Zmod.unsigned (N.v41748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41748 s i)) at 1.
  unfold R.v41748, N.v41748.
  rewrite ?node_41746.
  rewrite ?node_41747.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41749 (s : N.State) (i : N.Inputs) :
  R.v41749 (state s) (inputs i) = Zmod.unsigned (N.v41749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41749 s i)) at 1.
  unfold R.v41749, N.v41749.
  rewrite ?node_41745.
  rewrite ?node_41748.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41750 (s : N.State) (i : N.Inputs) :
  R.v41750 (state s) (inputs i) = Zmod.unsigned (N.v41750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41750 s i)) at 1.
  unfold R.v41750, N.v41750.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41751 (s : N.State) (i : N.Inputs) :
  R.v41751 (state s) (inputs i) = Zmod.unsigned (N.v41751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41751 s i)) at 1.
  unfold R.v41751, N.v41751.
  rewrite ?node_9293.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41752 (s : N.State) (i : N.Inputs) :
  R.v41752 (state s) (inputs i) = Zmod.unsigned (N.v41752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41752 s i)) at 1.
  unfold R.v41752, N.v41752.
  rewrite ?node_9289.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41753 (s : N.State) (i : N.Inputs) :
  R.v41753 (state s) (inputs i) = Zmod.unsigned (N.v41753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41753 s i)) at 1.
  unfold R.v41753, N.v41753.
  rewrite ?node_9287.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41754 (s : N.State) (i : N.Inputs) :
  R.v41754 (state s) (inputs i) = Zmod.unsigned (N.v41754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41754 s i)) at 1.
  unfold R.v41754, N.v41754.
  unfold R.v6, N.v6.
  rewrite ?node_9279.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41755 (s : N.State) (i : N.Inputs) :
  R.v41755 (state s) (inputs i) = Zmod.unsigned (N.v41755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41755 s i)) at 1.
  unfold R.v41755, N.v41755.
  unfold R.v6, N.v6.
  rewrite ?node_9272.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41756 (s : N.State) (i : N.Inputs) :
  R.v41756 (state s) (inputs i) = Zmod.unsigned (N.v41756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41756 s i)) at 1.
  unfold R.v41756, N.v41756.
  rewrite ?node_41754.
  rewrite ?node_41755.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41757 (s : N.State) (i : N.Inputs) :
  R.v41757 (state s) (inputs i) = Zmod.unsigned (N.v41757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41757 s i)) at 1.
  unfold R.v41757, N.v41757.
  unfold R.v16484, N.v16484.
  rewrite ?node_41756.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41758 (s : N.State) (i : N.Inputs) :
  R.v41758 (state s) (inputs i) = Zmod.unsigned (N.v41758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41758 s i)) at 1.
  unfold R.v41758, N.v41758.
  rewrite ?node_41751.
  rewrite ?node_41752.
  rewrite ?node_41753.
  rewrite ?node_41757.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41759 (s : N.State) (i : N.Inputs) :
  R.v41759 (state s) (inputs i) = Zmod.unsigned (N.v41759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41759 s i)) at 1.
  unfold R.v41759, N.v41759.
  unfold R.v6, N.v6.
  rewrite ?node_41758.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41760 (s : N.State) (i : N.Inputs) :
  R.v41760 (state s) (inputs i) = Zmod.unsigned (N.v41760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41760 s i)) at 1.
  unfold R.v41760, N.v41760.
  rewrite ?node_9294.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41761 (s : N.State) (i : N.Inputs) :
  R.v41761 (state s) (inputs i) = Zmod.unsigned (N.v41761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41761 s i)) at 1.
  unfold R.v41761, N.v41761.
  unfold R.v6, N.v6.
  rewrite ?node_9436.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41762 (s : N.State) (i : N.Inputs) :
  R.v41762 (state s) (inputs i) = Zmod.unsigned (N.v41762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41762 s i)) at 1.
  unfold R.v41762, N.v41762.
  unfold R.v6, N.v6.
  rewrite ?node_9486.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41763 (s : N.State) (i : N.Inputs) :
  R.v41763 (state s) (inputs i) = Zmod.unsigned (N.v41763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41763 s i)) at 1.
  unfold R.v41763, N.v41763.
  rewrite ?node_41760.
  rewrite ?node_41761.
  rewrite ?node_41762.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41764 (s : N.State) (i : N.Inputs) :
  R.v41764 (state s) (inputs i) = Zmod.unsigned (N.v41764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41764 s i)) at 1.
  unfold R.v41764, N.v41764.
  rewrite ?node_41759.
  rewrite ?node_41763.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41765 (s : N.State) (i : N.Inputs) :
  R.v41765 (state s) (inputs i) = Zmod.unsigned (N.v41765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41765 s i)) at 1.
  unfold R.v41765, N.v41765.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41766 (s : N.State) (i : N.Inputs) :
  R.v41766 (state s) (inputs i) = Zmod.unsigned (N.v41766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41766 s i)) at 1.
  unfold R.v41766, N.v41766.
  rewrite ?node_9287.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41767 (s : N.State) (i : N.Inputs) :
  R.v41767 (state s) (inputs i) = Zmod.unsigned (N.v41767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41767 s i)) at 1.
  unfold R.v41767, N.v41767.
  unfold R.v6, N.v6.
  rewrite ?node_9279.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41768 (s : N.State) (i : N.Inputs) :
  R.v41768 (state s) (inputs i) = Zmod.unsigned (N.v41768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41768 s i)) at 1.
  unfold R.v41768, N.v41768.
  unfold R.v6, N.v6.
  rewrite ?node_9272.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41769 (s : N.State) (i : N.Inputs) :
  R.v41769 (state s) (inputs i) = Zmod.unsigned (N.v41769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41769 s i)) at 1.
  unfold R.v41769, N.v41769.
  rewrite ?node_41767.
  rewrite ?node_41768.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41770 (s : N.State) (i : N.Inputs) :
  R.v41770 (state s) (inputs i) = Zmod.unsigned (N.v41770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41770 s i)) at 1.
  unfold R.v41770, N.v41770.
  unfold R.v16484, N.v16484.
  rewrite ?node_41769.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41771 (s : N.State) (i : N.Inputs) :
  R.v41771 (state s) (inputs i) = Zmod.unsigned (N.v41771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41771 s i)) at 1.
  unfold R.v41771, N.v41771.
  rewrite ?node_41766.
  rewrite ?node_41770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41772 (s : N.State) (i : N.Inputs) :
  R.v41772 (state s) (inputs i) = Zmod.unsigned (N.v41772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41772 s i)) at 1.
  unfold R.v41772, N.v41772.
  unfold R.v6, N.v6.
  rewrite ?node_41771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41773 (s : N.State) (i : N.Inputs) :
  R.v41773 (state s) (inputs i) = Zmod.unsigned (N.v41773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41773 s i)) at 1.
  unfold R.v41773, N.v41773.
  rewrite ?node_9288.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41774 (s : N.State) (i : N.Inputs) :
  R.v41774 (state s) (inputs i) = Zmod.unsigned (N.v41774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41774 s i)) at 1.
  unfold R.v41774, N.v41774.
  unfold R.v6, N.v6.
  rewrite ?node_9436.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41775 (s : N.State) (i : N.Inputs) :
  R.v41775 (state s) (inputs i) = Zmod.unsigned (N.v41775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41775 s i)) at 1.
  unfold R.v41775, N.v41775.
  rewrite ?node_41773.
  rewrite ?node_41774.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41776 (s : N.State) (i : N.Inputs) :
  R.v41776 (state s) (inputs i) = Zmod.unsigned (N.v41776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41776 s i)) at 1.
  unfold R.v41776, N.v41776.
  rewrite ?node_41772.
  rewrite ?node_41775.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41777 (s : N.State) (i : N.Inputs) :
  R.v41777 (state s) (inputs i) = Zmod.unsigned (N.v41777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41777 s i)) at 1.
  unfold R.v41777, N.v41777.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41778 (s : N.State) (i : N.Inputs) :
  R.v41778 (state s) (inputs i) = Zmod.unsigned (N.v41778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41778 s i)) at 1.
  unfold R.v41778, N.v41778.
  rewrite ?node_9293.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41779 (s : N.State) (i : N.Inputs) :
  R.v41779 (state s) (inputs i) = Zmod.unsigned (N.v41779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41779 s i)) at 1.
  unfold R.v41779, N.v41779.
  unfold R.v6, N.v6.
  rewrite ?node_9289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41780 (s : N.State) (i : N.Inputs) :
  R.v41780 (state s) (inputs i) = Zmod.unsigned (N.v41780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41780 s i)) at 1.
  unfold R.v41780, N.v41780.
  unfold R.v6, N.v6.
  rewrite ?node_9288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41781 (s : N.State) (i : N.Inputs) :
  R.v41781 (state s) (inputs i) = Zmod.unsigned (N.v41781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41781 s i)) at 1.
  unfold R.v41781, N.v41781.
  rewrite ?node_41779.
  rewrite ?node_41780.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41782 (s : N.State) (i : N.Inputs) :
  R.v41782 (state s) (inputs i) = Zmod.unsigned (N.v41782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41782 s i)) at 1.
  unfold R.v41782, N.v41782.
  unfold R.v16484, N.v16484.
  rewrite ?node_41781.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41783 (s : N.State) (i : N.Inputs) :
  R.v41783 (state s) (inputs i) = Zmod.unsigned (N.v41783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41783 s i)) at 1.
  unfold R.v41783, N.v41783.
  rewrite ?node_41778.
  rewrite ?node_41782.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41784 (s : N.State) (i : N.Inputs) :
  R.v41784 (state s) (inputs i) = Zmod.unsigned (N.v41784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41784 s i)) at 1.
  unfold R.v41784, N.v41784.
  unfold R.v6, N.v6.
  rewrite ?node_41783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41785 (s : N.State) (i : N.Inputs) :
  R.v41785 (state s) (inputs i) = Zmod.unsigned (N.v41785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41785 s i)) at 1.
  unfold R.v41785, N.v41785.
  rewrite ?node_9294.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41786 (s : N.State) (i : N.Inputs) :
  R.v41786 (state s) (inputs i) = Zmod.unsigned (N.v41786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41786 s i)) at 1.
  unfold R.v41786, N.v41786.
  unfold R.v6, N.v6.
  rewrite ?node_9486.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41787 (s : N.State) (i : N.Inputs) :
  R.v41787 (state s) (inputs i) = Zmod.unsigned (N.v41787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41787 s i)) at 1.
  unfold R.v41787, N.v41787.
  rewrite ?node_41785.
  rewrite ?node_41786.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41788 (s : N.State) (i : N.Inputs) :
  R.v41788 (state s) (inputs i) = Zmod.unsigned (N.v41788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41788 s i)) at 1.
  unfold R.v41788, N.v41788.
  rewrite ?node_41784.
  rewrite ?node_41787.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41789 (s : N.State) (i : N.Inputs) :
  R.v41789 (state s) (inputs i) = Zmod.unsigned (N.v41789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41789 s i)) at 1.
  unfold R.v41789, N.v41789.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41790 (s : N.State) (i : N.Inputs) :
  R.v41790 (state s) (inputs i) = Zmod.unsigned (N.v41790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41790 s i)) at 1.
  unfold R.v41790, N.v41790.
  rewrite ?node_9313.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41791 (s : N.State) (i : N.Inputs) :
  R.v41791 (state s) (inputs i) = Zmod.unsigned (N.v41791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41791 s i)) at 1.
  unfold R.v41791, N.v41791.
  rewrite ?node_9309.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41792 (s : N.State) (i : N.Inputs) :
  R.v41792 (state s) (inputs i) = Zmod.unsigned (N.v41792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41792 s i)) at 1.
  unfold R.v41792, N.v41792.
  rewrite ?node_9305.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41793 (s : N.State) (i : N.Inputs) :
  R.v41793 (state s) (inputs i) = Zmod.unsigned (N.v41793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41793 s i)) at 1.
  unfold R.v41793, N.v41793.
  unfold R.v6, N.v6.
  rewrite ?node_9301.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41794 (s : N.State) (i : N.Inputs) :
  R.v41794 (state s) (inputs i) = Zmod.unsigned (N.v41794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41794 s i)) at 1.
  unfold R.v41794, N.v41794.
  unfold R.v6, N.v6.
  rewrite ?node_9298.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41795 (s : N.State) (i : N.Inputs) :
  R.v41795 (state s) (inputs i) = Zmod.unsigned (N.v41795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41795 s i)) at 1.
  unfold R.v41795, N.v41795.
  rewrite ?node_41793.
  rewrite ?node_41794.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41796 (s : N.State) (i : N.Inputs) :
  R.v41796 (state s) (inputs i) = Zmod.unsigned (N.v41796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41796 s i)) at 1.
  unfold R.v41796, N.v41796.
  unfold R.v16484, N.v16484.
  rewrite ?node_41795.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41797 (s : N.State) (i : N.Inputs) :
  R.v41797 (state s) (inputs i) = Zmod.unsigned (N.v41797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41797 s i)) at 1.
  unfold R.v41797, N.v41797.
  rewrite ?node_41790.
  rewrite ?node_41791.
  rewrite ?node_41792.
  rewrite ?node_41796.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41798 (s : N.State) (i : N.Inputs) :
  R.v41798 (state s) (inputs i) = Zmod.unsigned (N.v41798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41798 s i)) at 1.
  unfold R.v41798, N.v41798.
  unfold R.v6, N.v6.
  rewrite ?node_41797.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41799 (s : N.State) (i : N.Inputs) :
  R.v41799 (state s) (inputs i) = Zmod.unsigned (N.v41799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41799 s i)) at 1.
  unfold R.v41799, N.v41799.
  rewrite ?node_9314.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41800 (s : N.State) (i : N.Inputs) :
  R.v41800 (state s) (inputs i) = Zmod.unsigned (N.v41800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41800 s i)) at 1.
  unfold R.v41800, N.v41800.
  unfold R.v6, N.v6.
  rewrite ?node_9456.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41801 (s : N.State) (i : N.Inputs) :
  R.v41801 (state s) (inputs i) = Zmod.unsigned (N.v41801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41801 s i)) at 1.
  unfold R.v41801, N.v41801.
  unfold R.v6, N.v6.
  rewrite ?node_9490.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41802 (s : N.State) (i : N.Inputs) :
  R.v41802 (state s) (inputs i) = Zmod.unsigned (N.v41802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41802 s i)) at 1.
  unfold R.v41802, N.v41802.
  rewrite ?node_41799.
  rewrite ?node_41800.
  rewrite ?node_41801.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41803 (s : N.State) (i : N.Inputs) :
  R.v41803 (state s) (inputs i) = Zmod.unsigned (N.v41803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41803 s i)) at 1.
  unfold R.v41803, N.v41803.
  rewrite ?node_41798.
  rewrite ?node_41802.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41804 (s : N.State) (i : N.Inputs) :
  R.v41804 (state s) (inputs i) = Zmod.unsigned (N.v41804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41804 s i)) at 1.
  unfold R.v41804, N.v41804.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41805 (s : N.State) (i : N.Inputs) :
  R.v41805 (state s) (inputs i) = Zmod.unsigned (N.v41805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41805 s i)) at 1.
  unfold R.v41805, N.v41805.
  rewrite ?node_9305.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41806 (s : N.State) (i : N.Inputs) :
  R.v41806 (state s) (inputs i) = Zmod.unsigned (N.v41806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41806 s i)) at 1.
  unfold R.v41806, N.v41806.
  unfold R.v6, N.v6.
  rewrite ?node_9301.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41807 (s : N.State) (i : N.Inputs) :
  R.v41807 (state s) (inputs i) = Zmod.unsigned (N.v41807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41807 s i)) at 1.
  unfold R.v41807, N.v41807.
  unfold R.v6, N.v6.
  rewrite ?node_9298.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41808 (s : N.State) (i : N.Inputs) :
  R.v41808 (state s) (inputs i) = Zmod.unsigned (N.v41808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41808 s i)) at 1.
  unfold R.v41808, N.v41808.
  rewrite ?node_41806.
  rewrite ?node_41807.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41809 (s : N.State) (i : N.Inputs) :
  R.v41809 (state s) (inputs i) = Zmod.unsigned (N.v41809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41809 s i)) at 1.
  unfold R.v41809, N.v41809.
  unfold R.v16484, N.v16484.
  rewrite ?node_41808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41810 (s : N.State) (i : N.Inputs) :
  R.v41810 (state s) (inputs i) = Zmod.unsigned (N.v41810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41810 s i)) at 1.
  unfold R.v41810, N.v41810.
  rewrite ?node_41805.
  rewrite ?node_41809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41811 (s : N.State) (i : N.Inputs) :
  R.v41811 (state s) (inputs i) = Zmod.unsigned (N.v41811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41811 s i)) at 1.
  unfold R.v41811, N.v41811.
  unfold R.v6, N.v6.
  rewrite ?node_41810.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41812 (s : N.State) (i : N.Inputs) :
  R.v41812 (state s) (inputs i) = Zmod.unsigned (N.v41812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41812 s i)) at 1.
  unfold R.v41812, N.v41812.
  rewrite ?node_9306.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41813 (s : N.State) (i : N.Inputs) :
  R.v41813 (state s) (inputs i) = Zmod.unsigned (N.v41813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41813 s i)) at 1.
  unfold R.v41813, N.v41813.
  unfold R.v6, N.v6.
  rewrite ?node_9456.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41814 (s : N.State) (i : N.Inputs) :
  R.v41814 (state s) (inputs i) = Zmod.unsigned (N.v41814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41814 s i)) at 1.
  unfold R.v41814, N.v41814.
  rewrite ?node_41812.
  rewrite ?node_41813.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41815 (s : N.State) (i : N.Inputs) :
  R.v41815 (state s) (inputs i) = Zmod.unsigned (N.v41815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41815 s i)) at 1.
  unfold R.v41815, N.v41815.
  rewrite ?node_41811.
  rewrite ?node_41814.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41816 (s : N.State) (i : N.Inputs) :
  R.v41816 (state s) (inputs i) = Zmod.unsigned (N.v41816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41816 s i)) at 1.
  unfold R.v41816, N.v41816.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41817 (s : N.State) (i : N.Inputs) :
  R.v41817 (state s) (inputs i) = Zmod.unsigned (N.v41817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41817 s i)) at 1.
  unfold R.v41817, N.v41817.
  rewrite ?node_9313.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41818 (s : N.State) (i : N.Inputs) :
  R.v41818 (state s) (inputs i) = Zmod.unsigned (N.v41818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41818 s i)) at 1.
  unfold R.v41818, N.v41818.
  unfold R.v6, N.v6.
  rewrite ?node_9309.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41819 (s : N.State) (i : N.Inputs) :
  R.v41819 (state s) (inputs i) = Zmod.unsigned (N.v41819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41819 s i)) at 1.
  unfold R.v41819, N.v41819.
  unfold R.v6, N.v6.
  rewrite ?node_9306.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41820 (s : N.State) (i : N.Inputs) :
  R.v41820 (state s) (inputs i) = Zmod.unsigned (N.v41820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41820 s i)) at 1.
  unfold R.v41820, N.v41820.
  rewrite ?node_41818.
  rewrite ?node_41819.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41821 (s : N.State) (i : N.Inputs) :
  R.v41821 (state s) (inputs i) = Zmod.unsigned (N.v41821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41821 s i)) at 1.
  unfold R.v41821, N.v41821.
  unfold R.v16484, N.v16484.
  rewrite ?node_41820.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41822 (s : N.State) (i : N.Inputs) :
  R.v41822 (state s) (inputs i) = Zmod.unsigned (N.v41822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41822 s i)) at 1.
  unfold R.v41822, N.v41822.
  rewrite ?node_41817.
  rewrite ?node_41821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41823 (s : N.State) (i : N.Inputs) :
  R.v41823 (state s) (inputs i) = Zmod.unsigned (N.v41823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41823 s i)) at 1.
  unfold R.v41823, N.v41823.
  unfold R.v6, N.v6.
  rewrite ?node_41822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41824 (s : N.State) (i : N.Inputs) :
  R.v41824 (state s) (inputs i) = Zmod.unsigned (N.v41824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41824 s i)) at 1.
  unfold R.v41824, N.v41824.
  rewrite ?node_9314.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41825 (s : N.State) (i : N.Inputs) :
  R.v41825 (state s) (inputs i) = Zmod.unsigned (N.v41825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41825 s i)) at 1.
  unfold R.v41825, N.v41825.
  unfold R.v6, N.v6.
  rewrite ?node_9490.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41826 (s : N.State) (i : N.Inputs) :
  R.v41826 (state s) (inputs i) = Zmod.unsigned (N.v41826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41826 s i)) at 1.
  unfold R.v41826, N.v41826.
  rewrite ?node_41824.
  rewrite ?node_41825.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41827 (s : N.State) (i : N.Inputs) :
  R.v41827 (state s) (inputs i) = Zmod.unsigned (N.v41827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41827 s i)) at 1.
  unfold R.v41827, N.v41827.
  rewrite ?node_41823.
  rewrite ?node_41826.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41828 (s : N.State) (i : N.Inputs) :
  R.v41828 (state s) (inputs i) = Zmod.unsigned (N.v41828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41828 s i)) at 1.
  unfold R.v41828, N.v41828.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41829 (s : N.State) (i : N.Inputs) :
  R.v41829 (state s) (inputs i) = Zmod.unsigned (N.v41829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41829 s i)) at 1.
  unfold R.v41829, N.v41829.
  rewrite ?node_9327.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41830 (s : N.State) (i : N.Inputs) :
  R.v41830 (state s) (inputs i) = Zmod.unsigned (N.v41830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41830 s i)) at 1.
  unfold R.v41830, N.v41830.
  rewrite ?node_9325.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41831 (s : N.State) (i : N.Inputs) :
  R.v41831 (state s) (inputs i) = Zmod.unsigned (N.v41831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41831 s i)) at 1.
  unfold R.v41831, N.v41831.
  unfold R.v6, N.v6.
  rewrite ?node_9321.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41832 (s : N.State) (i : N.Inputs) :
  R.v41832 (state s) (inputs i) = Zmod.unsigned (N.v41832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41832 s i)) at 1.
  unfold R.v41832, N.v41832.
  unfold R.v6, N.v6.
  rewrite ?node_9318.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41833 (s : N.State) (i : N.Inputs) :
  R.v41833 (state s) (inputs i) = Zmod.unsigned (N.v41833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41833 s i)) at 1.
  unfold R.v41833, N.v41833.
  rewrite ?node_41831.
  rewrite ?node_41832.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41834 (s : N.State) (i : N.Inputs) :
  R.v41834 (state s) (inputs i) = Zmod.unsigned (N.v41834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41834 s i)) at 1.
  unfold R.v41834, N.v41834.
  unfold R.v16484, N.v16484.
  rewrite ?node_41833.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41835 (s : N.State) (i : N.Inputs) :
  R.v41835 (state s) (inputs i) = Zmod.unsigned (N.v41835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41835 s i)) at 1.
  unfold R.v41835, N.v41835.
  rewrite ?node_41829.
  rewrite ?node_41830.
  rewrite ?node_41834.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41836 (s : N.State) (i : N.Inputs) :
  R.v41836 (state s) (inputs i) = Zmod.unsigned (N.v41836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41836 s i)) at 1.
  unfold R.v41836, N.v41836.
  unfold R.v6, N.v6.
  rewrite ?node_41835.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41837 (s : N.State) (i : N.Inputs) :
  R.v41837 (state s) (inputs i) = Zmod.unsigned (N.v41837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41837 s i)) at 1.
  unfold R.v41837, N.v41837.
  rewrite ?node_9328.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41838 (s : N.State) (i : N.Inputs) :
  R.v41838 (state s) (inputs i) = Zmod.unsigned (N.v41838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41838 s i)) at 1.
  unfold R.v41838, N.v41838.
  unfold R.v6, N.v6.
  rewrite ?node_9474.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41839 (s : N.State) (i : N.Inputs) :
  R.v41839 (state s) (inputs i) = Zmod.unsigned (N.v41839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41839 s i)) at 1.
  unfold R.v41839, N.v41839.
  unfold R.v6, N.v6.
  rewrite ?node_9492.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41840 (s : N.State) (i : N.Inputs) :
  R.v41840 (state s) (inputs i) = Zmod.unsigned (N.v41840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41840 s i)) at 1.
  unfold R.v41840, N.v41840.
  rewrite ?node_41837.
  rewrite ?node_41838.
  rewrite ?node_41839.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41841 (s : N.State) (i : N.Inputs) :
  R.v41841 (state s) (inputs i) = Zmod.unsigned (N.v41841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41841 s i)) at 1.
  unfold R.v41841, N.v41841.
  rewrite ?node_41836.
  rewrite ?node_41840.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41842 (s : N.State) (i : N.Inputs) :
  R.v41842 (state s) (inputs i) = Zmod.unsigned (N.v41842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41842 s i)) at 1.
  unfold R.v41842, N.v41842.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41843 (s : N.State) (i : N.Inputs) :
  R.v41843 (state s) (inputs i) = Zmod.unsigned (N.v41843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41843 s i)) at 1.
  unfold R.v41843, N.v41843.
  rewrite ?node_9325.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41844 (s : N.State) (i : N.Inputs) :
  R.v41844 (state s) (inputs i) = Zmod.unsigned (N.v41844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41844 s i)) at 1.
  unfold R.v41844, N.v41844.
  unfold R.v6, N.v6.
  rewrite ?node_9321.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41845 (s : N.State) (i : N.Inputs) :
  R.v41845 (state s) (inputs i) = Zmod.unsigned (N.v41845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41845 s i)) at 1.
  unfold R.v41845, N.v41845.
  unfold R.v6, N.v6.
  rewrite ?node_9318.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41846 (s : N.State) (i : N.Inputs) :
  R.v41846 (state s) (inputs i) = Zmod.unsigned (N.v41846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41846 s i)) at 1.
  unfold R.v41846, N.v41846.
  rewrite ?node_41844.
  rewrite ?node_41845.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41847 (s : N.State) (i : N.Inputs) :
  R.v41847 (state s) (inputs i) = Zmod.unsigned (N.v41847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41847 s i)) at 1.
  unfold R.v41847, N.v41847.
  unfold R.v16484, N.v16484.
  rewrite ?node_41846.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41848 (s : N.State) (i : N.Inputs) :
  R.v41848 (state s) (inputs i) = Zmod.unsigned (N.v41848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41848 s i)) at 1.
  unfold R.v41848, N.v41848.
  rewrite ?node_41843.
  rewrite ?node_41847.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41849 (s : N.State) (i : N.Inputs) :
  R.v41849 (state s) (inputs i) = Zmod.unsigned (N.v41849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41849 s i)) at 1.
  unfold R.v41849, N.v41849.
  unfold R.v6, N.v6.
  rewrite ?node_41848.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41850 (s : N.State) (i : N.Inputs) :
  R.v41850 (state s) (inputs i) = Zmod.unsigned (N.v41850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41850 s i)) at 1.
  unfold R.v41850, N.v41850.
  rewrite ?node_9326.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41851 (s : N.State) (i : N.Inputs) :
  R.v41851 (state s) (inputs i) = Zmod.unsigned (N.v41851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41851 s i)) at 1.
  unfold R.v41851, N.v41851.
  unfold R.v6, N.v6.
  rewrite ?node_9474.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41852 (s : N.State) (i : N.Inputs) :
  R.v41852 (state s) (inputs i) = Zmod.unsigned (N.v41852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41852 s i)) at 1.
  unfold R.v41852, N.v41852.
  rewrite ?node_41850.
  rewrite ?node_41851.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41853 (s : N.State) (i : N.Inputs) :
  R.v41853 (state s) (inputs i) = Zmod.unsigned (N.v41853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41853 s i)) at 1.
  unfold R.v41853, N.v41853.
  rewrite ?node_41849.
  rewrite ?node_41852.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41854 (s : N.State) (i : N.Inputs) :
  R.v41854 (state s) (inputs i) = Zmod.unsigned (N.v41854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41854 s i)) at 1.
  unfold R.v41854, N.v41854.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41855 (s : N.State) (i : N.Inputs) :
  R.v41855 (state s) (inputs i) = Zmod.unsigned (N.v41855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41855 s i)) at 1.
  unfold R.v41855, N.v41855.
  unfold R.v6, N.v6.
  rewrite ?node_9327.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41856 (s : N.State) (i : N.Inputs) :
  R.v41856 (state s) (inputs i) = Zmod.unsigned (N.v41856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41856 s i)) at 1.
  unfold R.v41856, N.v41856.
  unfold R.v6, N.v6.
  rewrite ?node_9326.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41857 (s : N.State) (i : N.Inputs) :
  R.v41857 (state s) (inputs i) = Zmod.unsigned (N.v41857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41857 s i)) at 1.
  unfold R.v41857, N.v41857.
  rewrite ?node_41855.
  rewrite ?node_41856.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41858 (s : N.State) (i : N.Inputs) :
  R.v41858 (state s) (inputs i) = Zmod.unsigned (N.v41858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41858 s i)) at 1.
  unfold R.v41858, N.v41858.
  unfold R.v16463, N.v16463.
  rewrite ?node_41857.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41859 (s : N.State) (i : N.Inputs) :
  R.v41859 (state s) (inputs i) = Zmod.unsigned (N.v41859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41859 s i)) at 1.
  unfold R.v41859, N.v41859.
  rewrite ?node_9328.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41860 (s : N.State) (i : N.Inputs) :
  R.v41860 (state s) (inputs i) = Zmod.unsigned (N.v41860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41860 s i)) at 1.
  unfold R.v41860, N.v41860.
  unfold R.v6, N.v6.
  rewrite ?node_9492.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41861 (s : N.State) (i : N.Inputs) :
  R.v41861 (state s) (inputs i) = Zmod.unsigned (N.v41861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41861 s i)) at 1.
  unfold R.v41861, N.v41861.
  rewrite ?node_41859.
  rewrite ?node_41860.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41862 (s : N.State) (i : N.Inputs) :
  R.v41862 (state s) (inputs i) = Zmod.unsigned (N.v41862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41862 s i)) at 1.
  unfold R.v41862, N.v41862.
  rewrite ?node_41858.
  rewrite ?node_41861.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41863 (s : N.State) (i : N.Inputs) :
  R.v41863 (state s) (inputs i) = Zmod.unsigned (N.v41863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41863 s i)) at 1.
  unfold R.v41863, N.v41863.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41864 (s : N.State) (i : N.Inputs) :
  R.v41864 (state s) (inputs i) = Zmod.unsigned (N.v41864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41864 s i)) at 1.
  unfold R.v41864, N.v41864.
  rewrite ?node_9406.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41865 (s : N.State) (i : N.Inputs) :
  R.v41865 (state s) (inputs i) = Zmod.unsigned (N.v41865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41865 s i)) at 1.
  unfold R.v41865, N.v41865.
  rewrite ?node_9402.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41866 (s : N.State) (i : N.Inputs) :
  R.v41866 (state s) (inputs i) = Zmod.unsigned (N.v41866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41866 s i)) at 1.
  unfold R.v41866, N.v41866.
  rewrite ?node_9394.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41867 (s : N.State) (i : N.Inputs) :
  R.v41867 (state s) (inputs i) = Zmod.unsigned (N.v41867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41867 s i)) at 1.
  unfold R.v41867, N.v41867.
  unfold R.v6, N.v6.
  rewrite ?node_9386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41868 (s : N.State) (i : N.Inputs) :
  R.v41868 (state s) (inputs i) = Zmod.unsigned (N.v41868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41868 s i)) at 1.
  unfold R.v41868, N.v41868.
  unfold R.v6, N.v6.
  rewrite ?node_9379.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41869 (s : N.State) (i : N.Inputs) :
  R.v41869 (state s) (inputs i) = Zmod.unsigned (N.v41869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41869 s i)) at 1.
  unfold R.v41869, N.v41869.
  rewrite ?node_41867.
  rewrite ?node_41868.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41870 (s : N.State) (i : N.Inputs) :
  R.v41870 (state s) (inputs i) = Zmod.unsigned (N.v41870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41870 s i)) at 1.
  unfold R.v41870, N.v41870.
  unfold R.v16484, N.v16484.
  rewrite ?node_41869.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41871 (s : N.State) (i : N.Inputs) :
  R.v41871 (state s) (inputs i) = Zmod.unsigned (N.v41871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41871 s i)) at 1.
  unfold R.v41871, N.v41871.
  rewrite ?node_41864.
  rewrite ?node_41865.
  rewrite ?node_41866.
  rewrite ?node_41870.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41872 (s : N.State) (i : N.Inputs) :
  R.v41872 (state s) (inputs i) = Zmod.unsigned (N.v41872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41872 s i)) at 1.
  unfold R.v41872, N.v41872.
  unfold R.v6, N.v6.
  rewrite ?node_41871.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41873 (s : N.State) (i : N.Inputs) :
  R.v41873 (state s) (inputs i) = Zmod.unsigned (N.v41873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41873 s i)) at 1.
  unfold R.v41873, N.v41873.
  rewrite ?node_9407.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41874 (s : N.State) (i : N.Inputs) :
  R.v41874 (state s) (inputs i) = Zmod.unsigned (N.v41874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41874 s i)) at 1.
  unfold R.v41874, N.v41874.
  unfold R.v6, N.v6.
  rewrite ?node_9551.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41875 (s : N.State) (i : N.Inputs) :
  R.v41875 (state s) (inputs i) = Zmod.unsigned (N.v41875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41875 s i)) at 1.
  unfold R.v41875, N.v41875.
  unfold R.v6, N.v6.
  rewrite ?node_9630.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41876 (s : N.State) (i : N.Inputs) :
  R.v41876 (state s) (inputs i) = Zmod.unsigned (N.v41876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41876 s i)) at 1.
  unfold R.v41876, N.v41876.
  rewrite ?node_41873.
  rewrite ?node_41874.
  rewrite ?node_41875.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41877 (s : N.State) (i : N.Inputs) :
  R.v41877 (state s) (inputs i) = Zmod.unsigned (N.v41877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41877 s i)) at 1.
  unfold R.v41877, N.v41877.
  rewrite ?node_41872.
  rewrite ?node_41876.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41878 (s : N.State) (i : N.Inputs) :
  R.v41878 (state s) (inputs i) = Zmod.unsigned (N.v41878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41878 s i)) at 1.
  unfold R.v41878, N.v41878.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41879 (s : N.State) (i : N.Inputs) :
  R.v41879 (state s) (inputs i) = Zmod.unsigned (N.v41879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41879 s i)) at 1.
  unfold R.v41879, N.v41879.
  rewrite ?node_9394.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41880 (s : N.State) (i : N.Inputs) :
  R.v41880 (state s) (inputs i) = Zmod.unsigned (N.v41880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41880 s i)) at 1.
  unfold R.v41880, N.v41880.
  unfold R.v6, N.v6.
  rewrite ?node_9386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41881 (s : N.State) (i : N.Inputs) :
  R.v41881 (state s) (inputs i) = Zmod.unsigned (N.v41881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41881 s i)) at 1.
  unfold R.v41881, N.v41881.
  unfold R.v6, N.v6.
  rewrite ?node_9379.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41882 (s : N.State) (i : N.Inputs) :
  R.v41882 (state s) (inputs i) = Zmod.unsigned (N.v41882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41882 s i)) at 1.
  unfold R.v41882, N.v41882.
  rewrite ?node_41880.
  rewrite ?node_41881.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41883 (s : N.State) (i : N.Inputs) :
  R.v41883 (state s) (inputs i) = Zmod.unsigned (N.v41883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41883 s i)) at 1.
  unfold R.v41883, N.v41883.
  unfold R.v16484, N.v16484.
  rewrite ?node_41882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41884 (s : N.State) (i : N.Inputs) :
  R.v41884 (state s) (inputs i) = Zmod.unsigned (N.v41884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41884 s i)) at 1.
  unfold R.v41884, N.v41884.
  rewrite ?node_41879.
  rewrite ?node_41883.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41885 (s : N.State) (i : N.Inputs) :
  R.v41885 (state s) (inputs i) = Zmod.unsigned (N.v41885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41885 s i)) at 1.
  unfold R.v41885, N.v41885.
  unfold R.v6, N.v6.
  rewrite ?node_41884.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41886 (s : N.State) (i : N.Inputs) :
  R.v41886 (state s) (inputs i) = Zmod.unsigned (N.v41886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41886 s i)) at 1.
  unfold R.v41886, N.v41886.
  rewrite ?node_9395.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41887 (s : N.State) (i : N.Inputs) :
  R.v41887 (state s) (inputs i) = Zmod.unsigned (N.v41887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41887 s i)) at 1.
  unfold R.v41887, N.v41887.
  unfold R.v6, N.v6.
  rewrite ?node_9551.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41888 (s : N.State) (i : N.Inputs) :
  R.v41888 (state s) (inputs i) = Zmod.unsigned (N.v41888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41888 s i)) at 1.
  unfold R.v41888, N.v41888.
  rewrite ?node_41886.
  rewrite ?node_41887.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41889 (s : N.State) (i : N.Inputs) :
  R.v41889 (state s) (inputs i) = Zmod.unsigned (N.v41889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41889 s i)) at 1.
  unfold R.v41889, N.v41889.
  rewrite ?node_41885.
  rewrite ?node_41888.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41890 (s : N.State) (i : N.Inputs) :
  R.v41890 (state s) (inputs i) = Zmod.unsigned (N.v41890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41890 s i)) at 1.
  unfold R.v41890, N.v41890.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41891 (s : N.State) (i : N.Inputs) :
  R.v41891 (state s) (inputs i) = Zmod.unsigned (N.v41891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41891 s i)) at 1.
  unfold R.v41891, N.v41891.
  rewrite ?node_9406.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41892 (s : N.State) (i : N.Inputs) :
  R.v41892 (state s) (inputs i) = Zmod.unsigned (N.v41892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41892 s i)) at 1.
  unfold R.v41892, N.v41892.
  unfold R.v6, N.v6.
  rewrite ?node_9402.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41893 (s : N.State) (i : N.Inputs) :
  R.v41893 (state s) (inputs i) = Zmod.unsigned (N.v41893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41893 s i)) at 1.
  unfold R.v41893, N.v41893.
  unfold R.v6, N.v6.
  rewrite ?node_9395.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41894 (s : N.State) (i : N.Inputs) :
  R.v41894 (state s) (inputs i) = Zmod.unsigned (N.v41894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41894 s i)) at 1.
  unfold R.v41894, N.v41894.
  rewrite ?node_41892.
  rewrite ?node_41893.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41895 (s : N.State) (i : N.Inputs) :
  R.v41895 (state s) (inputs i) = Zmod.unsigned (N.v41895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41895 s i)) at 1.
  unfold R.v41895, N.v41895.
  unfold R.v16484, N.v16484.
  rewrite ?node_41894.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41896 (s : N.State) (i : N.Inputs) :
  R.v41896 (state s) (inputs i) = Zmod.unsigned (N.v41896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41896 s i)) at 1.
  unfold R.v41896, N.v41896.
  rewrite ?node_41891.
  rewrite ?node_41895.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41897 (s : N.State) (i : N.Inputs) :
  R.v41897 (state s) (inputs i) = Zmod.unsigned (N.v41897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41897 s i)) at 1.
  unfold R.v41897, N.v41897.
  unfold R.v6, N.v6.
  rewrite ?node_41896.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41898 (s : N.State) (i : N.Inputs) :
  R.v41898 (state s) (inputs i) = Zmod.unsigned (N.v41898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41898 s i)) at 1.
  unfold R.v41898, N.v41898.
  rewrite ?node_9407.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41899 (s : N.State) (i : N.Inputs) :
  R.v41899 (state s) (inputs i) = Zmod.unsigned (N.v41899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41899 s i)) at 1.
  unfold R.v41899, N.v41899.
  unfold R.v6, N.v6.
  rewrite ?node_9630.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41900 (s : N.State) (i : N.Inputs) :
  R.v41900 (state s) (inputs i) = Zmod.unsigned (N.v41900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41900 s i)) at 1.
  unfold R.v41900, N.v41900.
  rewrite ?node_41898.
  rewrite ?node_41899.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41901 (s : N.State) (i : N.Inputs) :
  R.v41901 (state s) (inputs i) = Zmod.unsigned (N.v41901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41901 s i)) at 1.
  unfold R.v41901, N.v41901.
  rewrite ?node_41897.
  rewrite ?node_41900.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41902 (s : N.State) (i : N.Inputs) :
  R.v41902 (state s) (inputs i) = Zmod.unsigned (N.v41902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41902 s i)) at 1.
  unfold R.v41902, N.v41902.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41903 (s : N.State) (i : N.Inputs) :
  R.v41903 (state s) (inputs i) = Zmod.unsigned (N.v41903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41903 s i)) at 1.
  unfold R.v41903, N.v41903.
  rewrite ?node_9436.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41904 (s : N.State) (i : N.Inputs) :
  R.v41904 (state s) (inputs i) = Zmod.unsigned (N.v41904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41904 s i)) at 1.
  unfold R.v41904, N.v41904.
  rewrite ?node_9432.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41905 (s : N.State) (i : N.Inputs) :
  R.v41905 (state s) (inputs i) = Zmod.unsigned (N.v41905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41905 s i)) at 1.
  unfold R.v41905, N.v41905.
  rewrite ?node_9429.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41906 (s : N.State) (i : N.Inputs) :
  R.v41906 (state s) (inputs i) = Zmod.unsigned (N.v41906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41906 s i)) at 1.
  unfold R.v41906, N.v41906.
  unfold R.v6, N.v6.
  rewrite ?node_9421.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41907 (s : N.State) (i : N.Inputs) :
  R.v41907 (state s) (inputs i) = Zmod.unsigned (N.v41907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41907 s i)) at 1.
  unfold R.v41907, N.v41907.
  unfold R.v6, N.v6.
  rewrite ?node_9414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41908 (s : N.State) (i : N.Inputs) :
  R.v41908 (state s) (inputs i) = Zmod.unsigned (N.v41908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41908 s i)) at 1.
  unfold R.v41908, N.v41908.
  rewrite ?node_41906.
  rewrite ?node_41907.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41909 (s : N.State) (i : N.Inputs) :
  R.v41909 (state s) (inputs i) = Zmod.unsigned (N.v41909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41909 s i)) at 1.
  unfold R.v41909, N.v41909.
  unfold R.v16484, N.v16484.
  rewrite ?node_41908.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41910 (s : N.State) (i : N.Inputs) :
  R.v41910 (state s) (inputs i) = Zmod.unsigned (N.v41910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41910 s i)) at 1.
  unfold R.v41910, N.v41910.
  rewrite ?node_41903.
  rewrite ?node_41904.
  rewrite ?node_41905.
  rewrite ?node_41909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41911 (s : N.State) (i : N.Inputs) :
  R.v41911 (state s) (inputs i) = Zmod.unsigned (N.v41911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41911 s i)) at 1.
  unfold R.v41911, N.v41911.
  unfold R.v6, N.v6.
  rewrite ?node_41910.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41912 (s : N.State) (i : N.Inputs) :
  R.v41912 (state s) (inputs i) = Zmod.unsigned (N.v41912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41912 s i)) at 1.
  unfold R.v41912, N.v41912.
  rewrite ?node_9437.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41913 (s : N.State) (i : N.Inputs) :
  R.v41913 (state s) (inputs i) = Zmod.unsigned (N.v41913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41913 s i)) at 1.
  unfold R.v41913, N.v41913.
  unfold R.v6, N.v6.
  rewrite ?node_9581.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41914 (s : N.State) (i : N.Inputs) :
  R.v41914 (state s) (inputs i) = Zmod.unsigned (N.v41914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41914 s i)) at 1.
  unfold R.v41914, N.v41914.
  unfold R.v6, N.v6.
  rewrite ?node_9633.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41915 (s : N.State) (i : N.Inputs) :
  R.v41915 (state s) (inputs i) = Zmod.unsigned (N.v41915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41915 s i)) at 1.
  unfold R.v41915, N.v41915.
  rewrite ?node_41912.
  rewrite ?node_41913.
  rewrite ?node_41914.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41916 (s : N.State) (i : N.Inputs) :
  R.v41916 (state s) (inputs i) = Zmod.unsigned (N.v41916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41916 s i)) at 1.
  unfold R.v41916, N.v41916.
  rewrite ?node_41911.
  rewrite ?node_41915.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41917 (s : N.State) (i : N.Inputs) :
  R.v41917 (state s) (inputs i) = Zmod.unsigned (N.v41917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41917 s i)) at 1.
  unfold R.v41917, N.v41917.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41918 (s : N.State) (i : N.Inputs) :
  R.v41918 (state s) (inputs i) = Zmod.unsigned (N.v41918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41918 s i)) at 1.
  unfold R.v41918, N.v41918.
  rewrite ?node_9429.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41919 (s : N.State) (i : N.Inputs) :
  R.v41919 (state s) (inputs i) = Zmod.unsigned (N.v41919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41919 s i)) at 1.
  unfold R.v41919, N.v41919.
  unfold R.v6, N.v6.
  rewrite ?node_9421.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41920 (s : N.State) (i : N.Inputs) :
  R.v41920 (state s) (inputs i) = Zmod.unsigned (N.v41920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41920 s i)) at 1.
  unfold R.v41920, N.v41920.
  unfold R.v6, N.v6.
  rewrite ?node_9414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41921 (s : N.State) (i : N.Inputs) :
  R.v41921 (state s) (inputs i) = Zmod.unsigned (N.v41921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41921 s i)) at 1.
  unfold R.v41921, N.v41921.
  rewrite ?node_41919.
  rewrite ?node_41920.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41922 (s : N.State) (i : N.Inputs) :
  R.v41922 (state s) (inputs i) = Zmod.unsigned (N.v41922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41922 s i)) at 1.
  unfold R.v41922, N.v41922.
  unfold R.v16484, N.v16484.
  rewrite ?node_41921.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41923 (s : N.State) (i : N.Inputs) :
  R.v41923 (state s) (inputs i) = Zmod.unsigned (N.v41923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41923 s i)) at 1.
  unfold R.v41923, N.v41923.
  rewrite ?node_41918.
  rewrite ?node_41922.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41924 (s : N.State) (i : N.Inputs) :
  R.v41924 (state s) (inputs i) = Zmod.unsigned (N.v41924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41924 s i)) at 1.
  unfold R.v41924, N.v41924.
  unfold R.v6, N.v6.
  rewrite ?node_41923.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41925 (s : N.State) (i : N.Inputs) :
  R.v41925 (state s) (inputs i) = Zmod.unsigned (N.v41925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41925 s i)) at 1.
  unfold R.v41925, N.v41925.
  rewrite ?node_9430.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41926 (s : N.State) (i : N.Inputs) :
  R.v41926 (state s) (inputs i) = Zmod.unsigned (N.v41926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41926 s i)) at 1.
  unfold R.v41926, N.v41926.
  unfold R.v6, N.v6.
  rewrite ?node_9581.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41927 (s : N.State) (i : N.Inputs) :
  R.v41927 (state s) (inputs i) = Zmod.unsigned (N.v41927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41927 s i)) at 1.
  unfold R.v41927, N.v41927.
  rewrite ?node_41925.
  rewrite ?node_41926.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41928 (s : N.State) (i : N.Inputs) :
  R.v41928 (state s) (inputs i) = Zmod.unsigned (N.v41928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41928 s i)) at 1.
  unfold R.v41928, N.v41928.
  rewrite ?node_41924.
  rewrite ?node_41927.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41929 (s : N.State) (i : N.Inputs) :
  R.v41929 (state s) (inputs i) = Zmod.unsigned (N.v41929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41929 s i)) at 1.
  unfold R.v41929, N.v41929.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41930 (s : N.State) (i : N.Inputs) :
  R.v41930 (state s) (inputs i) = Zmod.unsigned (N.v41930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41930 s i)) at 1.
  unfold R.v41930, N.v41930.
  rewrite ?node_9436.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41931 (s : N.State) (i : N.Inputs) :
  R.v41931 (state s) (inputs i) = Zmod.unsigned (N.v41931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41931 s i)) at 1.
  unfold R.v41931, N.v41931.
  unfold R.v6, N.v6.
  rewrite ?node_9432.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41932 (s : N.State) (i : N.Inputs) :
  R.v41932 (state s) (inputs i) = Zmod.unsigned (N.v41932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41932 s i)) at 1.
  unfold R.v41932, N.v41932.
  unfold R.v6, N.v6.
  rewrite ?node_9430.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41933 (s : N.State) (i : N.Inputs) :
  R.v41933 (state s) (inputs i) = Zmod.unsigned (N.v41933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41933 s i)) at 1.
  unfold R.v41933, N.v41933.
  rewrite ?node_41931.
  rewrite ?node_41932.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41934 (s : N.State) (i : N.Inputs) :
  R.v41934 (state s) (inputs i) = Zmod.unsigned (N.v41934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41934 s i)) at 1.
  unfold R.v41934, N.v41934.
  unfold R.v16484, N.v16484.
  rewrite ?node_41933.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41935 (s : N.State) (i : N.Inputs) :
  R.v41935 (state s) (inputs i) = Zmod.unsigned (N.v41935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41935 s i)) at 1.
  unfold R.v41935, N.v41935.
  rewrite ?node_41930.
  rewrite ?node_41934.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41936 (s : N.State) (i : N.Inputs) :
  R.v41936 (state s) (inputs i) = Zmod.unsigned (N.v41936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41936 s i)) at 1.
  unfold R.v41936, N.v41936.
  unfold R.v6, N.v6.
  rewrite ?node_41935.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41937 (s : N.State) (i : N.Inputs) :
  R.v41937 (state s) (inputs i) = Zmod.unsigned (N.v41937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41937 s i)) at 1.
  unfold R.v41937, N.v41937.
  rewrite ?node_9437.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41938 (s : N.State) (i : N.Inputs) :
  R.v41938 (state s) (inputs i) = Zmod.unsigned (N.v41938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41938 s i)) at 1.
  unfold R.v41938, N.v41938.
  unfold R.v6, N.v6.
  rewrite ?node_9633.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41939 (s : N.State) (i : N.Inputs) :
  R.v41939 (state s) (inputs i) = Zmod.unsigned (N.v41939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41939 s i)) at 1.
  unfold R.v41939, N.v41939.
  rewrite ?node_41937.
  rewrite ?node_41938.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41940 (s : N.State) (i : N.Inputs) :
  R.v41940 (state s) (inputs i) = Zmod.unsigned (N.v41940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41940 s i)) at 1.
  unfold R.v41940, N.v41940.
  rewrite ?node_41936.
  rewrite ?node_41939.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41941 (s : N.State) (i : N.Inputs) :
  R.v41941 (state s) (inputs i) = Zmod.unsigned (N.v41941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41941 s i)) at 1.
  unfold R.v41941, N.v41941.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41942 (s : N.State) (i : N.Inputs) :
  R.v41942 (state s) (inputs i) = Zmod.unsigned (N.v41942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41942 s i)) at 1.
  unfold R.v41942, N.v41942.
  rewrite ?node_9456.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41943 (s : N.State) (i : N.Inputs) :
  R.v41943 (state s) (inputs i) = Zmod.unsigned (N.v41943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41943 s i)) at 1.
  unfold R.v41943, N.v41943.
  rewrite ?node_9452.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41944 (s : N.State) (i : N.Inputs) :
  R.v41944 (state s) (inputs i) = Zmod.unsigned (N.v41944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41944 s i)) at 1.
  unfold R.v41944, N.v41944.
  rewrite ?node_9448.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41945 (s : N.State) (i : N.Inputs) :
  R.v41945 (state s) (inputs i) = Zmod.unsigned (N.v41945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41945 s i)) at 1.
  unfold R.v41945, N.v41945.
  unfold R.v6, N.v6.
  rewrite ?node_9444.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41946 (s : N.State) (i : N.Inputs) :
  R.v41946 (state s) (inputs i) = Zmod.unsigned (N.v41946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41946 s i)) at 1.
  unfold R.v41946, N.v41946.
  unfold R.v6, N.v6.
  rewrite ?node_9441.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41947 (s : N.State) (i : N.Inputs) :
  R.v41947 (state s) (inputs i) = Zmod.unsigned (N.v41947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41947 s i)) at 1.
  unfold R.v41947, N.v41947.
  rewrite ?node_41945.
  rewrite ?node_41946.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41948 (s : N.State) (i : N.Inputs) :
  R.v41948 (state s) (inputs i) = Zmod.unsigned (N.v41948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41948 s i)) at 1.
  unfold R.v41948, N.v41948.
  unfold R.v16484, N.v16484.
  rewrite ?node_41947.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41949 (s : N.State) (i : N.Inputs) :
  R.v41949 (state s) (inputs i) = Zmod.unsigned (N.v41949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41949 s i)) at 1.
  unfold R.v41949, N.v41949.
  rewrite ?node_41942.
  rewrite ?node_41943.
  rewrite ?node_41944.
  rewrite ?node_41948.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41950 (s : N.State) (i : N.Inputs) :
  R.v41950 (state s) (inputs i) = Zmod.unsigned (N.v41950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41950 s i)) at 1.
  unfold R.v41950, N.v41950.
  unfold R.v6, N.v6.
  rewrite ?node_41949.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41951 (s : N.State) (i : N.Inputs) :
  R.v41951 (state s) (inputs i) = Zmod.unsigned (N.v41951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41951 s i)) at 1.
  unfold R.v41951, N.v41951.
  rewrite ?node_9457.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41952 (s : N.State) (i : N.Inputs) :
  R.v41952 (state s) (inputs i) = Zmod.unsigned (N.v41952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41952 s i)) at 1.
  unfold R.v41952, N.v41952.
  unfold R.v6, N.v6.
  rewrite ?node_9601.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41953 (s : N.State) (i : N.Inputs) :
  R.v41953 (state s) (inputs i) = Zmod.unsigned (N.v41953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41953 s i)) at 1.
  unfold R.v41953, N.v41953.
  unfold R.v6, N.v6.
  rewrite ?node_9637.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41954 (s : N.State) (i : N.Inputs) :
  R.v41954 (state s) (inputs i) = Zmod.unsigned (N.v41954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41954 s i)) at 1.
  unfold R.v41954, N.v41954.
  rewrite ?node_41951.
  rewrite ?node_41952.
  rewrite ?node_41953.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41955 (s : N.State) (i : N.Inputs) :
  R.v41955 (state s) (inputs i) = Zmod.unsigned (N.v41955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41955 s i)) at 1.
  unfold R.v41955, N.v41955.
  rewrite ?node_41950.
  rewrite ?node_41954.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41956 (s : N.State) (i : N.Inputs) :
  R.v41956 (state s) (inputs i) = Zmod.unsigned (N.v41956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41956 s i)) at 1.
  unfold R.v41956, N.v41956.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41957 (s : N.State) (i : N.Inputs) :
  R.v41957 (state s) (inputs i) = Zmod.unsigned (N.v41957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41957 s i)) at 1.
  unfold R.v41957, N.v41957.
  rewrite ?node_9448.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41958 (s : N.State) (i : N.Inputs) :
  R.v41958 (state s) (inputs i) = Zmod.unsigned (N.v41958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41958 s i)) at 1.
  unfold R.v41958, N.v41958.
  unfold R.v6, N.v6.
  rewrite ?node_9444.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41959 (s : N.State) (i : N.Inputs) :
  R.v41959 (state s) (inputs i) = Zmod.unsigned (N.v41959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41959 s i)) at 1.
  unfold R.v41959, N.v41959.
  unfold R.v6, N.v6.
  rewrite ?node_9441.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41960 (s : N.State) (i : N.Inputs) :
  R.v41960 (state s) (inputs i) = Zmod.unsigned (N.v41960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41960 s i)) at 1.
  unfold R.v41960, N.v41960.
  rewrite ?node_41958.
  rewrite ?node_41959.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41961 (s : N.State) (i : N.Inputs) :
  R.v41961 (state s) (inputs i) = Zmod.unsigned (N.v41961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41961 s i)) at 1.
  unfold R.v41961, N.v41961.
  unfold R.v16484, N.v16484.
  rewrite ?node_41960.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41962 (s : N.State) (i : N.Inputs) :
  R.v41962 (state s) (inputs i) = Zmod.unsigned (N.v41962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41962 s i)) at 1.
  unfold R.v41962, N.v41962.
  rewrite ?node_41957.
  rewrite ?node_41961.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41963 (s : N.State) (i : N.Inputs) :
  R.v41963 (state s) (inputs i) = Zmod.unsigned (N.v41963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41963 s i)) at 1.
  unfold R.v41963, N.v41963.
  unfold R.v6, N.v6.
  rewrite ?node_41962.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41964 (s : N.State) (i : N.Inputs) :
  R.v41964 (state s) (inputs i) = Zmod.unsigned (N.v41964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41964 s i)) at 1.
  unfold R.v41964, N.v41964.
  rewrite ?node_9449.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41965 (s : N.State) (i : N.Inputs) :
  R.v41965 (state s) (inputs i) = Zmod.unsigned (N.v41965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41965 s i)) at 1.
  unfold R.v41965, N.v41965.
  unfold R.v6, N.v6.
  rewrite ?node_9601.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41966 (s : N.State) (i : N.Inputs) :
  R.v41966 (state s) (inputs i) = Zmod.unsigned (N.v41966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41966 s i)) at 1.
  unfold R.v41966, N.v41966.
  rewrite ?node_41964.
  rewrite ?node_41965.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41967 (s : N.State) (i : N.Inputs) :
  R.v41967 (state s) (inputs i) = Zmod.unsigned (N.v41967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41967 s i)) at 1.
  unfold R.v41967, N.v41967.
  rewrite ?node_41963.
  rewrite ?node_41966.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41968 (s : N.State) (i : N.Inputs) :
  R.v41968 (state s) (inputs i) = Zmod.unsigned (N.v41968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41968 s i)) at 1.
  unfold R.v41968, N.v41968.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41969 (s : N.State) (i : N.Inputs) :
  R.v41969 (state s) (inputs i) = Zmod.unsigned (N.v41969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41969 s i)) at 1.
  unfold R.v41969, N.v41969.
  rewrite ?node_9456.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41970 (s : N.State) (i : N.Inputs) :
  R.v41970 (state s) (inputs i) = Zmod.unsigned (N.v41970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41970 s i)) at 1.
  unfold R.v41970, N.v41970.
  unfold R.v6, N.v6.
  rewrite ?node_9452.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41971 (s : N.State) (i : N.Inputs) :
  R.v41971 (state s) (inputs i) = Zmod.unsigned (N.v41971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41971 s i)) at 1.
  unfold R.v41971, N.v41971.
  unfold R.v6, N.v6.
  rewrite ?node_9449.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41972 (s : N.State) (i : N.Inputs) :
  R.v41972 (state s) (inputs i) = Zmod.unsigned (N.v41972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41972 s i)) at 1.
  unfold R.v41972, N.v41972.
  rewrite ?node_41970.
  rewrite ?node_41971.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41973 (s : N.State) (i : N.Inputs) :
  R.v41973 (state s) (inputs i) = Zmod.unsigned (N.v41973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41973 s i)) at 1.
  unfold R.v41973, N.v41973.
  unfold R.v16484, N.v16484.
  rewrite ?node_41972.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41974 (s : N.State) (i : N.Inputs) :
  R.v41974 (state s) (inputs i) = Zmod.unsigned (N.v41974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41974 s i)) at 1.
  unfold R.v41974, N.v41974.
  rewrite ?node_41969.
  rewrite ?node_41973.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41975 (s : N.State) (i : N.Inputs) :
  R.v41975 (state s) (inputs i) = Zmod.unsigned (N.v41975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41975 s i)) at 1.
  unfold R.v41975, N.v41975.
  unfold R.v6, N.v6.
  rewrite ?node_41974.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41976 (s : N.State) (i : N.Inputs) :
  R.v41976 (state s) (inputs i) = Zmod.unsigned (N.v41976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41976 s i)) at 1.
  unfold R.v41976, N.v41976.
  rewrite ?node_9457.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41977 (s : N.State) (i : N.Inputs) :
  R.v41977 (state s) (inputs i) = Zmod.unsigned (N.v41977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41977 s i)) at 1.
  unfold R.v41977, N.v41977.
  unfold R.v6, N.v6.
  rewrite ?node_9637.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41978 (s : N.State) (i : N.Inputs) :
  R.v41978 (state s) (inputs i) = Zmod.unsigned (N.v41978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41978 s i)) at 1.
  unfold R.v41978, N.v41978.
  rewrite ?node_41976.
  rewrite ?node_41977.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41979 (s : N.State) (i : N.Inputs) :
  R.v41979 (state s) (inputs i) = Zmod.unsigned (N.v41979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41979 s i)) at 1.
  unfold R.v41979, N.v41979.
  rewrite ?node_41975.
  rewrite ?node_41978.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41980 (s : N.State) (i : N.Inputs) :
  R.v41980 (state s) (inputs i) = Zmod.unsigned (N.v41980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41980 s i)) at 1.
  unfold R.v41980, N.v41980.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41981 (s : N.State) (i : N.Inputs) :
  R.v41981 (state s) (inputs i) = Zmod.unsigned (N.v41981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41981 s i)) at 1.
  unfold R.v41981, N.v41981.
  rewrite ?node_9474.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41982 (s : N.State) (i : N.Inputs) :
  R.v41982 (state s) (inputs i) = Zmod.unsigned (N.v41982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41982 s i)) at 1.
  unfold R.v41982, N.v41982.
  rewrite ?node_9470.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41983 (s : N.State) (i : N.Inputs) :
  R.v41983 (state s) (inputs i) = Zmod.unsigned (N.v41983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41983 s i)) at 1.
  unfold R.v41983, N.v41983.
  rewrite ?node_9468.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41984 (s : N.State) (i : N.Inputs) :
  R.v41984 (state s) (inputs i) = Zmod.unsigned (N.v41984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41984 s i)) at 1.
  unfold R.v41984, N.v41984.
  unfold R.v6, N.v6.
  rewrite ?node_9464.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41985 (s : N.State) (i : N.Inputs) :
  R.v41985 (state s) (inputs i) = Zmod.unsigned (N.v41985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41985 s i)) at 1.
  unfold R.v41985, N.v41985.
  unfold R.v6, N.v6.
  rewrite ?node_9461.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41986 (s : N.State) (i : N.Inputs) :
  R.v41986 (state s) (inputs i) = Zmod.unsigned (N.v41986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41986 s i)) at 1.
  unfold R.v41986, N.v41986.
  rewrite ?node_41984.
  rewrite ?node_41985.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41987 (s : N.State) (i : N.Inputs) :
  R.v41987 (state s) (inputs i) = Zmod.unsigned (N.v41987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41987 s i)) at 1.
  unfold R.v41987, N.v41987.
  unfold R.v16484, N.v16484.
  rewrite ?node_41986.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41988 (s : N.State) (i : N.Inputs) :
  R.v41988 (state s) (inputs i) = Zmod.unsigned (N.v41988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41988 s i)) at 1.
  unfold R.v41988, N.v41988.
  rewrite ?node_41981.
  rewrite ?node_41982.
  rewrite ?node_41983.
  rewrite ?node_41987.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41989 (s : N.State) (i : N.Inputs) :
  R.v41989 (state s) (inputs i) = Zmod.unsigned (N.v41989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41989 s i)) at 1.
  unfold R.v41989, N.v41989.
  unfold R.v6, N.v6.
  rewrite ?node_41988.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41990 (s : N.State) (i : N.Inputs) :
  R.v41990 (state s) (inputs i) = Zmod.unsigned (N.v41990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41990 s i)) at 1.
  unfold R.v41990, N.v41990.
  rewrite ?node_9475.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41991 (s : N.State) (i : N.Inputs) :
  R.v41991 (state s) (inputs i) = Zmod.unsigned (N.v41991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41991 s i)) at 1.
  unfold R.v41991, N.v41991.
  unfold R.v6, N.v6.
  rewrite ?node_9621.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41992 (s : N.State) (i : N.Inputs) :
  R.v41992 (state s) (inputs i) = Zmod.unsigned (N.v41992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41992 s i)) at 1.
  unfold R.v41992, N.v41992.
  unfold R.v6, N.v6.
  rewrite ?node_9641.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41993 (s : N.State) (i : N.Inputs) :
  R.v41993 (state s) (inputs i) = Zmod.unsigned (N.v41993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41993 s i)) at 1.
  unfold R.v41993, N.v41993.
  rewrite ?node_41990.
  rewrite ?node_41991.
  rewrite ?node_41992.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41994 (s : N.State) (i : N.Inputs) :
  R.v41994 (state s) (inputs i) = Zmod.unsigned (N.v41994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41994 s i)) at 1.
  unfold R.v41994, N.v41994.
  rewrite ?node_41989.
  rewrite ?node_41993.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41995 (s : N.State) (i : N.Inputs) :
  R.v41995 (state s) (inputs i) = Zmod.unsigned (N.v41995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41995 s i)) at 1.
  unfold R.v41995, N.v41995.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41996 (s : N.State) (i : N.Inputs) :
  R.v41996 (state s) (inputs i) = Zmod.unsigned (N.v41996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41996 s i)) at 1.
  unfold R.v41996, N.v41996.
  rewrite ?node_9468.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41997 (s : N.State) (i : N.Inputs) :
  R.v41997 (state s) (inputs i) = Zmod.unsigned (N.v41997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41997 s i)) at 1.
  unfold R.v41997, N.v41997.
  unfold R.v6, N.v6.
  rewrite ?node_9464.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41998 (s : N.State) (i : N.Inputs) :
  R.v41998 (state s) (inputs i) = Zmod.unsigned (N.v41998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41998 s i)) at 1.
  unfold R.v41998, N.v41998.
  unfold R.v6, N.v6.
  rewrite ?node_9461.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_41999 (s : N.State) (i : N.Inputs) :
  R.v41999 (state s) (inputs i) = Zmod.unsigned (N.v41999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v41999 s i)) at 1.
  unfold R.v41999, N.v41999.
  rewrite ?node_41997.
  rewrite ?node_41998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
