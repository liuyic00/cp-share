(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes057.
Lemma node_58000 (s : N.State) (i : N.Inputs) :
  R.v58000 (state s) (inputs i) = Zmod.unsigned (N.v58000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58000 s i)) at 1.
  unfold R.v58000, N.v58000.
  unfold R.v6, N.v6.
  rewrite ?node_10279.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58001 (s : N.State) (i : N.Inputs) :
  R.v58001 (state s) (inputs i) = Zmod.unsigned (N.v58001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58001 s i)) at 1.
  unfold R.v58001, N.v58001.
  rewrite ?node_57999.
  rewrite ?node_58000.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58002 (s : N.State) (i : N.Inputs) :
  R.v58002 (state s) (inputs i) = Zmod.unsigned (N.v58002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58002 s i)) at 1.
  unfold R.v58002, N.v58002.
  rewrite ?node_57998.
  rewrite ?node_58001.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58003 (s : N.State) (i : N.Inputs) :
  R.v58003 (state s) (inputs i) = Zmod.unsigned (N.v58003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58003 s i)) at 1.
  unfold R.v58003, N.v58003.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58004 (s : N.State) (i : N.Inputs) :
  R.v58004 (state s) (inputs i) = Zmod.unsigned (N.v58004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58004 s i)) at 1.
  unfold R.v58004, N.v58004.
  rewrite ?node_10274.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58005 (s : N.State) (i : N.Inputs) :
  R.v58005 (state s) (inputs i) = Zmod.unsigned (N.v58005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58005 s i)) at 1.
  unfold R.v58005, N.v58005.
  unfold R.v6, N.v6.
  rewrite ?node_10270.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58006 (s : N.State) (i : N.Inputs) :
  R.v58006 (state s) (inputs i) = Zmod.unsigned (N.v58006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58006 s i)) at 1.
  unfold R.v58006, N.v58006.
  unfold R.v6, N.v6.
  rewrite ?node_10267.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58007 (s : N.State) (i : N.Inputs) :
  R.v58007 (state s) (inputs i) = Zmod.unsigned (N.v58007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58007 s i)) at 1.
  unfold R.v58007, N.v58007.
  rewrite ?node_58005.
  rewrite ?node_58006.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58008 (s : N.State) (i : N.Inputs) :
  R.v58008 (state s) (inputs i) = Zmod.unsigned (N.v58008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58008 s i)) at 1.
  unfold R.v58008, N.v58008.
  unfold R.v16484, N.v16484.
  rewrite ?node_58007.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58009 (s : N.State) (i : N.Inputs) :
  R.v58009 (state s) (inputs i) = Zmod.unsigned (N.v58009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58009 s i)) at 1.
  unfold R.v58009, N.v58009.
  rewrite ?node_58004.
  rewrite ?node_58008.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58010 (s : N.State) (i : N.Inputs) :
  R.v58010 (state s) (inputs i) = Zmod.unsigned (N.v58010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58010 s i)) at 1.
  unfold R.v58010, N.v58010.
  unfold R.v6, N.v6.
  rewrite ?node_58009.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58011 (s : N.State) (i : N.Inputs) :
  R.v58011 (state s) (inputs i) = Zmod.unsigned (N.v58011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58011 s i)) at 1.
  unfold R.v58011, N.v58011.
  rewrite ?node_10275.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58012 (s : N.State) (i : N.Inputs) :
  R.v58012 (state s) (inputs i) = Zmod.unsigned (N.v58012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58012 s i)) at 1.
  unfold R.v58012, N.v58012.
  unfold R.v6, N.v6.
  rewrite ?node_10437.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58013 (s : N.State) (i : N.Inputs) :
  R.v58013 (state s) (inputs i) = Zmod.unsigned (N.v58013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58013 s i)) at 1.
  unfold R.v58013, N.v58013.
  rewrite ?node_58011.
  rewrite ?node_58012.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58014 (s : N.State) (i : N.Inputs) :
  R.v58014 (state s) (inputs i) = Zmod.unsigned (N.v58014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58014 s i)) at 1.
  unfold R.v58014, N.v58014.
  rewrite ?node_58010.
  rewrite ?node_58013.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58015 (s : N.State) (i : N.Inputs) :
  R.v58015 (state s) (inputs i) = Zmod.unsigned (N.v58015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58015 s i)) at 1.
  unfold R.v58015, N.v58015.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58016 (s : N.State) (i : N.Inputs) :
  R.v58016 (state s) (inputs i) = Zmod.unsigned (N.v58016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58016 s i)) at 1.
  unfold R.v58016, N.v58016.
  rewrite ?node_10432.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58017 (s : N.State) (i : N.Inputs) :
  R.v58017 (state s) (inputs i) = Zmod.unsigned (N.v58017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58017 s i)) at 1.
  unfold R.v58017, N.v58017.
  unfold R.v6, N.v6.
  rewrite ?node_10428.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58018 (s : N.State) (i : N.Inputs) :
  R.v58018 (state s) (inputs i) = Zmod.unsigned (N.v58018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58018 s i)) at 1.
  unfold R.v58018, N.v58018.
  unfold R.v6, N.v6.
  rewrite ?node_10425.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58019 (s : N.State) (i : N.Inputs) :
  R.v58019 (state s) (inputs i) = Zmod.unsigned (N.v58019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58019 s i)) at 1.
  unfold R.v58019, N.v58019.
  rewrite ?node_58017.
  rewrite ?node_58018.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58020 (s : N.State) (i : N.Inputs) :
  R.v58020 (state s) (inputs i) = Zmod.unsigned (N.v58020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58020 s i)) at 1.
  unfold R.v58020, N.v58020.
  unfold R.v16484, N.v16484.
  rewrite ?node_58019.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58021 (s : N.State) (i : N.Inputs) :
  R.v58021 (state s) (inputs i) = Zmod.unsigned (N.v58021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58021 s i)) at 1.
  unfold R.v58021, N.v58021.
  rewrite ?node_58016.
  rewrite ?node_58020.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58022 (s : N.State) (i : N.Inputs) :
  R.v58022 (state s) (inputs i) = Zmod.unsigned (N.v58022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58022 s i)) at 1.
  unfold R.v58022, N.v58022.
  unfold R.v6, N.v6.
  rewrite ?node_58021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58023 (s : N.State) (i : N.Inputs) :
  R.v58023 (state s) (inputs i) = Zmod.unsigned (N.v58023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58023 s i)) at 1.
  unfold R.v58023, N.v58023.
  rewrite ?node_10433.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58024 (s : N.State) (i : N.Inputs) :
  R.v58024 (state s) (inputs i) = Zmod.unsigned (N.v58024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58024 s i)) at 1.
  unfold R.v58024, N.v58024.
  unfold R.v6, N.v6.
  rewrite ?node_10597.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58025 (s : N.State) (i : N.Inputs) :
  R.v58025 (state s) (inputs i) = Zmod.unsigned (N.v58025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58025 s i)) at 1.
  unfold R.v58025, N.v58025.
  rewrite ?node_58023.
  rewrite ?node_58024.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58026 (s : N.State) (i : N.Inputs) :
  R.v58026 (state s) (inputs i) = Zmod.unsigned (N.v58026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58026 s i)) at 1.
  unfold R.v58026, N.v58026.
  rewrite ?node_58022.
  rewrite ?node_58025.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58027 (s : N.State) (i : N.Inputs) :
  R.v58027 (state s) (inputs i) = Zmod.unsigned (N.v58027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58027 s i)) at 1.
  unfold R.v58027, N.v58027.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58028 (s : N.State) (i : N.Inputs) :
  R.v58028 (state s) (inputs i) = Zmod.unsigned (N.v58028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58028 s i)) at 1.
  unfold R.v58028, N.v58028.
  rewrite ?node_10592.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58029 (s : N.State) (i : N.Inputs) :
  R.v58029 (state s) (inputs i) = Zmod.unsigned (N.v58029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58029 s i)) at 1.
  unfold R.v58029, N.v58029.
  unfold R.v6, N.v6.
  rewrite ?node_10588.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58030 (s : N.State) (i : N.Inputs) :
  R.v58030 (state s) (inputs i) = Zmod.unsigned (N.v58030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58030 s i)) at 1.
  unfold R.v58030, N.v58030.
  unfold R.v6, N.v6.
  rewrite ?node_10585.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58031 (s : N.State) (i : N.Inputs) :
  R.v58031 (state s) (inputs i) = Zmod.unsigned (N.v58031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58031 s i)) at 1.
  unfold R.v58031, N.v58031.
  rewrite ?node_58029.
  rewrite ?node_58030.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58032 (s : N.State) (i : N.Inputs) :
  R.v58032 (state s) (inputs i) = Zmod.unsigned (N.v58032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58032 s i)) at 1.
  unfold R.v58032, N.v58032.
  unfold R.v16484, N.v16484.
  rewrite ?node_58031.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58033 (s : N.State) (i : N.Inputs) :
  R.v58033 (state s) (inputs i) = Zmod.unsigned (N.v58033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58033 s i)) at 1.
  unfold R.v58033, N.v58033.
  rewrite ?node_58028.
  rewrite ?node_58032.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58034 (s : N.State) (i : N.Inputs) :
  R.v58034 (state s) (inputs i) = Zmod.unsigned (N.v58034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58034 s i)) at 1.
  unfold R.v58034, N.v58034.
  unfold R.v6, N.v6.
  rewrite ?node_58033.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58035 (s : N.State) (i : N.Inputs) :
  R.v58035 (state s) (inputs i) = Zmod.unsigned (N.v58035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58035 s i)) at 1.
  unfold R.v58035, N.v58035.
  rewrite ?node_10593.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58036 (s : N.State) (i : N.Inputs) :
  R.v58036 (state s) (inputs i) = Zmod.unsigned (N.v58036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58036 s i)) at 1.
  unfold R.v58036, N.v58036.
  unfold R.v6, N.v6.
  rewrite ?node_10758.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58037 (s : N.State) (i : N.Inputs) :
  R.v58037 (state s) (inputs i) = Zmod.unsigned (N.v58037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58037 s i)) at 1.
  unfold R.v58037, N.v58037.
  rewrite ?node_58035.
  rewrite ?node_58036.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58038 (s : N.State) (i : N.Inputs) :
  R.v58038 (state s) (inputs i) = Zmod.unsigned (N.v58038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58038 s i)) at 1.
  unfold R.v58038, N.v58038.
  rewrite ?node_58034.
  rewrite ?node_58037.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58039 (s : N.State) (i : N.Inputs) :
  R.v58039 (state s) (inputs i) = Zmod.unsigned (N.v58039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58039 s i)) at 1.
  unfold R.v58039, N.v58039.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58040 (s : N.State) (i : N.Inputs) :
  R.v58040 (state s) (inputs i) = Zmod.unsigned (N.v58040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58040 s i)) at 1.
  unfold R.v58040, N.v58040.
  rewrite ?node_10753.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58041 (s : N.State) (i : N.Inputs) :
  R.v58041 (state s) (inputs i) = Zmod.unsigned (N.v58041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58041 s i)) at 1.
  unfold R.v58041, N.v58041.
  unfold R.v6, N.v6.
  rewrite ?node_10749.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58042 (s : N.State) (i : N.Inputs) :
  R.v58042 (state s) (inputs i) = Zmod.unsigned (N.v58042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58042 s i)) at 1.
  unfold R.v58042, N.v58042.
  unfold R.v6, N.v6.
  rewrite ?node_10746.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58043 (s : N.State) (i : N.Inputs) :
  R.v58043 (state s) (inputs i) = Zmod.unsigned (N.v58043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58043 s i)) at 1.
  unfold R.v58043, N.v58043.
  rewrite ?node_58041.
  rewrite ?node_58042.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58044 (s : N.State) (i : N.Inputs) :
  R.v58044 (state s) (inputs i) = Zmod.unsigned (N.v58044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58044 s i)) at 1.
  unfold R.v58044, N.v58044.
  unfold R.v16484, N.v16484.
  rewrite ?node_58043.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58045 (s : N.State) (i : N.Inputs) :
  R.v58045 (state s) (inputs i) = Zmod.unsigned (N.v58045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58045 s i)) at 1.
  unfold R.v58045, N.v58045.
  rewrite ?node_58040.
  rewrite ?node_58044.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58046 (s : N.State) (i : N.Inputs) :
  R.v58046 (state s) (inputs i) = Zmod.unsigned (N.v58046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58046 s i)) at 1.
  unfold R.v58046, N.v58046.
  unfold R.v6, N.v6.
  rewrite ?node_58045.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58047 (s : N.State) (i : N.Inputs) :
  R.v58047 (state s) (inputs i) = Zmod.unsigned (N.v58047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58047 s i)) at 1.
  unfold R.v58047, N.v58047.
  rewrite ?node_10754.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58048 (s : N.State) (i : N.Inputs) :
  R.v58048 (state s) (inputs i) = Zmod.unsigned (N.v58048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58048 s i)) at 1.
  unfold R.v58048, N.v58048.
  unfold R.v6, N.v6.
  rewrite ?node_10919.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58049 (s : N.State) (i : N.Inputs) :
  R.v58049 (state s) (inputs i) = Zmod.unsigned (N.v58049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58049 s i)) at 1.
  unfold R.v58049, N.v58049.
  rewrite ?node_58047.
  rewrite ?node_58048.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58050 (s : N.State) (i : N.Inputs) :
  R.v58050 (state s) (inputs i) = Zmod.unsigned (N.v58050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58050 s i)) at 1.
  unfold R.v58050, N.v58050.
  rewrite ?node_58046.
  rewrite ?node_58049.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58051 (s : N.State) (i : N.Inputs) :
  R.v58051 (state s) (inputs i) = Zmod.unsigned (N.v58051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58051 s i)) at 1.
  unfold R.v58051, N.v58051.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58052 (s : N.State) (i : N.Inputs) :
  R.v58052 (state s) (inputs i) = Zmod.unsigned (N.v58052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58052 s i)) at 1.
  unfold R.v58052, N.v58052.
  rewrite ?node_10914.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58053 (s : N.State) (i : N.Inputs) :
  R.v58053 (state s) (inputs i) = Zmod.unsigned (N.v58053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58053 s i)) at 1.
  unfold R.v58053, N.v58053.
  unfold R.v6, N.v6.
  rewrite ?node_10910.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58054 (s : N.State) (i : N.Inputs) :
  R.v58054 (state s) (inputs i) = Zmod.unsigned (N.v58054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58054 s i)) at 1.
  unfold R.v58054, N.v58054.
  unfold R.v6, N.v6.
  rewrite ?node_10905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58055 (s : N.State) (i : N.Inputs) :
  R.v58055 (state s) (inputs i) = Zmod.unsigned (N.v58055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58055 s i)) at 1.
  unfold R.v58055, N.v58055.
  rewrite ?node_58053.
  rewrite ?node_58054.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58056 (s : N.State) (i : N.Inputs) :
  R.v58056 (state s) (inputs i) = Zmod.unsigned (N.v58056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58056 s i)) at 1.
  unfold R.v58056, N.v58056.
  unfold R.v16484, N.v16484.
  rewrite ?node_58055.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58057 (s : N.State) (i : N.Inputs) :
  R.v58057 (state s) (inputs i) = Zmod.unsigned (N.v58057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58057 s i)) at 1.
  unfold R.v58057, N.v58057.
  rewrite ?node_58052.
  rewrite ?node_58056.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58058 (s : N.State) (i : N.Inputs) :
  R.v58058 (state s) (inputs i) = Zmod.unsigned (N.v58058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58058 s i)) at 1.
  unfold R.v58058, N.v58058.
  unfold R.v6, N.v6.
  rewrite ?node_58057.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58059 (s : N.State) (i : N.Inputs) :
  R.v58059 (state s) (inputs i) = Zmod.unsigned (N.v58059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58059 s i)) at 1.
  unfold R.v58059, N.v58059.
  rewrite ?node_10915.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58060 (s : N.State) (i : N.Inputs) :
  R.v58060 (state s) (inputs i) = Zmod.unsigned (N.v58060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58060 s i)) at 1.
  unfold R.v58060, N.v58060.
  unfold R.v6, N.v6.
  rewrite ?node_11080.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58061 (s : N.State) (i : N.Inputs) :
  R.v58061 (state s) (inputs i) = Zmod.unsigned (N.v58061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58061 s i)) at 1.
  unfold R.v58061, N.v58061.
  rewrite ?node_58059.
  rewrite ?node_58060.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58062 (s : N.State) (i : N.Inputs) :
  R.v58062 (state s) (inputs i) = Zmod.unsigned (N.v58062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58062 s i)) at 1.
  unfold R.v58062, N.v58062.
  rewrite ?node_58058.
  rewrite ?node_58061.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58063 (s : N.State) (i : N.Inputs) :
  R.v58063 (state s) (inputs i) = Zmod.unsigned (N.v58063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58063 s i)) at 1.
  unfold R.v58063, N.v58063.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58064 (s : N.State) (i : N.Inputs) :
  R.v58064 (state s) (inputs i) = Zmod.unsigned (N.v58064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58064 s i)) at 1.
  unfold R.v58064, N.v58064.
  rewrite ?node_11075.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58065 (s : N.State) (i : N.Inputs) :
  R.v58065 (state s) (inputs i) = Zmod.unsigned (N.v58065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58065 s i)) at 1.
  unfold R.v58065, N.v58065.
  rewrite ?node_11073.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58066 (s : N.State) (i : N.Inputs) :
  R.v58066 (state s) (inputs i) = Zmod.unsigned (N.v58066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58066 s i)) at 1.
  unfold R.v58066, N.v58066.
  unfold R.v6, N.v6.
  rewrite ?node_11069.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58067 (s : N.State) (i : N.Inputs) :
  R.v58067 (state s) (inputs i) = Zmod.unsigned (N.v58067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58067 s i)) at 1.
  unfold R.v58067, N.v58067.
  unfold R.v6, N.v6.
  rewrite ?node_11064.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58068 (s : N.State) (i : N.Inputs) :
  R.v58068 (state s) (inputs i) = Zmod.unsigned (N.v58068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58068 s i)) at 1.
  unfold R.v58068, N.v58068.
  rewrite ?node_58066.
  rewrite ?node_58067.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58069 (s : N.State) (i : N.Inputs) :
  R.v58069 (state s) (inputs i) = Zmod.unsigned (N.v58069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58069 s i)) at 1.
  unfold R.v58069, N.v58069.
  unfold R.v16484, N.v16484.
  rewrite ?node_58068.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58070 (s : N.State) (i : N.Inputs) :
  R.v58070 (state s) (inputs i) = Zmod.unsigned (N.v58070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58070 s i)) at 1.
  unfold R.v58070, N.v58070.
  rewrite ?node_58064.
  rewrite ?node_58065.
  rewrite ?node_58069.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58071 (s : N.State) (i : N.Inputs) :
  R.v58071 (state s) (inputs i) = Zmod.unsigned (N.v58071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58071 s i)) at 1.
  unfold R.v58071, N.v58071.
  unfold R.v6, N.v6.
  rewrite ?node_58070.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58072 (s : N.State) (i : N.Inputs) :
  R.v58072 (state s) (inputs i) = Zmod.unsigned (N.v58072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58072 s i)) at 1.
  unfold R.v58072, N.v58072.
  rewrite ?node_11076.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58073 (s : N.State) (i : N.Inputs) :
  R.v58073 (state s) (inputs i) = Zmod.unsigned (N.v58073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58073 s i)) at 1.
  unfold R.v58073, N.v58073.
  unfold R.v6, N.v6.
  rewrite ?node_11238.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58074 (s : N.State) (i : N.Inputs) :
  R.v58074 (state s) (inputs i) = Zmod.unsigned (N.v58074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58074 s i)) at 1.
  unfold R.v58074, N.v58074.
  unfold R.v6, N.v6.
  rewrite ?node_11240.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58075 (s : N.State) (i : N.Inputs) :
  R.v58075 (state s) (inputs i) = Zmod.unsigned (N.v58075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58075 s i)) at 1.
  unfold R.v58075, N.v58075.
  rewrite ?node_58072.
  rewrite ?node_58073.
  rewrite ?node_58074.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58076 (s : N.State) (i : N.Inputs) :
  R.v58076 (state s) (inputs i) = Zmod.unsigned (N.v58076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58076 s i)) at 1.
  unfold R.v58076, N.v58076.
  rewrite ?node_58071.
  rewrite ?node_58075.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58077 (s : N.State) (i : N.Inputs) :
  R.v58077 (state s) (inputs i) = Zmod.unsigned (N.v58077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58077 s i)) at 1.
  unfold R.v58077, N.v58077.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58078 (s : N.State) (i : N.Inputs) :
  R.v58078 (state s) (inputs i) = Zmod.unsigned (N.v58078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58078 s i)) at 1.
  unfold R.v58078, N.v58078.
  rewrite ?node_11073.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58079 (s : N.State) (i : N.Inputs) :
  R.v58079 (state s) (inputs i) = Zmod.unsigned (N.v58079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58079 s i)) at 1.
  unfold R.v58079, N.v58079.
  unfold R.v6, N.v6.
  rewrite ?node_11069.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58080 (s : N.State) (i : N.Inputs) :
  R.v58080 (state s) (inputs i) = Zmod.unsigned (N.v58080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58080 s i)) at 1.
  unfold R.v58080, N.v58080.
  unfold R.v6, N.v6.
  rewrite ?node_11064.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58081 (s : N.State) (i : N.Inputs) :
  R.v58081 (state s) (inputs i) = Zmod.unsigned (N.v58081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58081 s i)) at 1.
  unfold R.v58081, N.v58081.
  rewrite ?node_58079.
  rewrite ?node_58080.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58082 (s : N.State) (i : N.Inputs) :
  R.v58082 (state s) (inputs i) = Zmod.unsigned (N.v58082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58082 s i)) at 1.
  unfold R.v58082, N.v58082.
  unfold R.v16484, N.v16484.
  rewrite ?node_58081.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58083 (s : N.State) (i : N.Inputs) :
  R.v58083 (state s) (inputs i) = Zmod.unsigned (N.v58083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58083 s i)) at 1.
  unfold R.v58083, N.v58083.
  rewrite ?node_58078.
  rewrite ?node_58082.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58084 (s : N.State) (i : N.Inputs) :
  R.v58084 (state s) (inputs i) = Zmod.unsigned (N.v58084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58084 s i)) at 1.
  unfold R.v58084, N.v58084.
  unfold R.v6, N.v6.
  rewrite ?node_58083.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58085 (s : N.State) (i : N.Inputs) :
  R.v58085 (state s) (inputs i) = Zmod.unsigned (N.v58085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58085 s i)) at 1.
  unfold R.v58085, N.v58085.
  rewrite ?node_11074.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58086 (s : N.State) (i : N.Inputs) :
  R.v58086 (state s) (inputs i) = Zmod.unsigned (N.v58086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58086 s i)) at 1.
  unfold R.v58086, N.v58086.
  unfold R.v6, N.v6.
  rewrite ?node_11238.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58087 (s : N.State) (i : N.Inputs) :
  R.v58087 (state s) (inputs i) = Zmod.unsigned (N.v58087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58087 s i)) at 1.
  unfold R.v58087, N.v58087.
  rewrite ?node_58085.
  rewrite ?node_58086.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58088 (s : N.State) (i : N.Inputs) :
  R.v58088 (state s) (inputs i) = Zmod.unsigned (N.v58088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58088 s i)) at 1.
  unfold R.v58088, N.v58088.
  rewrite ?node_58084.
  rewrite ?node_58087.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58089 (s : N.State) (i : N.Inputs) :
  R.v58089 (state s) (inputs i) = Zmod.unsigned (N.v58089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58089 s i)) at 1.
  unfold R.v58089, N.v58089.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58090 (s : N.State) (i : N.Inputs) :
  R.v58090 (state s) (inputs i) = Zmod.unsigned (N.v58090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58090 s i)) at 1.
  unfold R.v58090, N.v58090.
  unfold R.v6, N.v6.
  rewrite ?node_11075.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58091 (s : N.State) (i : N.Inputs) :
  R.v58091 (state s) (inputs i) = Zmod.unsigned (N.v58091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58091 s i)) at 1.
  unfold R.v58091, N.v58091.
  unfold R.v6, N.v6.
  rewrite ?node_11074.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58092 (s : N.State) (i : N.Inputs) :
  R.v58092 (state s) (inputs i) = Zmod.unsigned (N.v58092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58092 s i)) at 1.
  unfold R.v58092, N.v58092.
  rewrite ?node_58090.
  rewrite ?node_58091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58093 (s : N.State) (i : N.Inputs) :
  R.v58093 (state s) (inputs i) = Zmod.unsigned (N.v58093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58093 s i)) at 1.
  unfold R.v58093, N.v58093.
  unfold R.v16463, N.v16463.
  rewrite ?node_58092.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58094 (s : N.State) (i : N.Inputs) :
  R.v58094 (state s) (inputs i) = Zmod.unsigned (N.v58094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58094 s i)) at 1.
  unfold R.v58094, N.v58094.
  rewrite ?node_11076.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58095 (s : N.State) (i : N.Inputs) :
  R.v58095 (state s) (inputs i) = Zmod.unsigned (N.v58095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58095 s i)) at 1.
  unfold R.v58095, N.v58095.
  unfold R.v6, N.v6.
  rewrite ?node_11240.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58096 (s : N.State) (i : N.Inputs) :
  R.v58096 (state s) (inputs i) = Zmod.unsigned (N.v58096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58096 s i)) at 1.
  unfold R.v58096, N.v58096.
  rewrite ?node_58094.
  rewrite ?node_58095.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58097 (s : N.State) (i : N.Inputs) :
  R.v58097 (state s) (inputs i) = Zmod.unsigned (N.v58097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58097 s i)) at 1.
  unfold R.v58097, N.v58097.
  rewrite ?node_58093.
  rewrite ?node_58096.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58098 (s : N.State) (i : N.Inputs) :
  R.v58098 (state s) (inputs i) = Zmod.unsigned (N.v58098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58098 s i)) at 1.
  unfold R.v58098, N.v58098.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58099 (s : N.State) (i : N.Inputs) :
  R.v58099 (state s) (inputs i) = Zmod.unsigned (N.v58099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58099 s i)) at 1.
  unfold R.v58099, N.v58099.
  rewrite ?node_11233.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58100 (s : N.State) (i : N.Inputs) :
  R.v58100 (state s) (inputs i) = Zmod.unsigned (N.v58100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58100 s i)) at 1.
  unfold R.v58100, N.v58100.
  unfold R.v6, N.v6.
  rewrite ?node_11231.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58101 (s : N.State) (i : N.Inputs) :
  R.v58101 (state s) (inputs i) = Zmod.unsigned (N.v58101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58101 s i)) at 1.
  unfold R.v58101, N.v58101.
  unfold R.v6, N.v6.
  rewrite ?node_11228.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58102 (s : N.State) (i : N.Inputs) :
  R.v58102 (state s) (inputs i) = Zmod.unsigned (N.v58102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58102 s i)) at 1.
  unfold R.v58102, N.v58102.
  rewrite ?node_58100.
  rewrite ?node_58101.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58103 (s : N.State) (i : N.Inputs) :
  R.v58103 (state s) (inputs i) = Zmod.unsigned (N.v58103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58103 s i)) at 1.
  unfold R.v58103, N.v58103.
  unfold R.v16484, N.v16484.
  rewrite ?node_58102.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58104 (s : N.State) (i : N.Inputs) :
  R.v58104 (state s) (inputs i) = Zmod.unsigned (N.v58104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58104 s i)) at 1.
  unfold R.v58104, N.v58104.
  rewrite ?node_58099.
  rewrite ?node_58103.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58105 (s : N.State) (i : N.Inputs) :
  R.v58105 (state s) (inputs i) = Zmod.unsigned (N.v58105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58105 s i)) at 1.
  unfold R.v58105, N.v58105.
  unfold R.v6, N.v6.
  rewrite ?node_58104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58106 (s : N.State) (i : N.Inputs) :
  R.v58106 (state s) (inputs i) = Zmod.unsigned (N.v58106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58106 s i)) at 1.
  unfold R.v58106, N.v58106.
  rewrite ?node_11234.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58107 (s : N.State) (i : N.Inputs) :
  R.v58107 (state s) (inputs i) = Zmod.unsigned (N.v58107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58107 s i)) at 1.
  unfold R.v58107, N.v58107.
  unfold R.v6, N.v6.
  rewrite ?node_11394.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58108 (s : N.State) (i : N.Inputs) :
  R.v58108 (state s) (inputs i) = Zmod.unsigned (N.v58108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58108 s i)) at 1.
  unfold R.v58108, N.v58108.
  rewrite ?node_58106.
  rewrite ?node_58107.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58109 (s : N.State) (i : N.Inputs) :
  R.v58109 (state s) (inputs i) = Zmod.unsigned (N.v58109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58109 s i)) at 1.
  unfold R.v58109, N.v58109.
  rewrite ?node_58105.
  rewrite ?node_58108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58110 (s : N.State) (i : N.Inputs) :
  R.v58110 (state s) (inputs i) = Zmod.unsigned (N.v58110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58110 s i)) at 1.
  unfold R.v58110, N.v58110.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58111 (s : N.State) (i : N.Inputs) :
  R.v58111 (state s) (inputs i) = Zmod.unsigned (N.v58111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58111 s i)) at 1.
  unfold R.v58111, N.v58111.
  rewrite ?node_11389.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58112 (s : N.State) (i : N.Inputs) :
  R.v58112 (state s) (inputs i) = Zmod.unsigned (N.v58112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58112 s i)) at 1.
  unfold R.v58112, N.v58112.
  unfold R.v6, N.v6.
  rewrite ?node_11385.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58113 (s : N.State) (i : N.Inputs) :
  R.v58113 (state s) (inputs i) = Zmod.unsigned (N.v58113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58113 s i)) at 1.
  unfold R.v58113, N.v58113.
  unfold R.v6, N.v6.
  rewrite ?node_11382.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58114 (s : N.State) (i : N.Inputs) :
  R.v58114 (state s) (inputs i) = Zmod.unsigned (N.v58114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58114 s i)) at 1.
  unfold R.v58114, N.v58114.
  rewrite ?node_58112.
  rewrite ?node_58113.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58115 (s : N.State) (i : N.Inputs) :
  R.v58115 (state s) (inputs i) = Zmod.unsigned (N.v58115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58115 s i)) at 1.
  unfold R.v58115, N.v58115.
  unfold R.v16484, N.v16484.
  rewrite ?node_58114.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58116 (s : N.State) (i : N.Inputs) :
  R.v58116 (state s) (inputs i) = Zmod.unsigned (N.v58116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58116 s i)) at 1.
  unfold R.v58116, N.v58116.
  rewrite ?node_58111.
  rewrite ?node_58115.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58117 (s : N.State) (i : N.Inputs) :
  R.v58117 (state s) (inputs i) = Zmod.unsigned (N.v58117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58117 s i)) at 1.
  unfold R.v58117, N.v58117.
  unfold R.v6, N.v6.
  rewrite ?node_58116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58118 (s : N.State) (i : N.Inputs) :
  R.v58118 (state s) (inputs i) = Zmod.unsigned (N.v58118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58118 s i)) at 1.
  unfold R.v58118, N.v58118.
  rewrite ?node_11390.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58119 (s : N.State) (i : N.Inputs) :
  R.v58119 (state s) (inputs i) = Zmod.unsigned (N.v58119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58119 s i)) at 1.
  unfold R.v58119, N.v58119.
  unfold R.v6, N.v6.
  rewrite ?node_11545.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58120 (s : N.State) (i : N.Inputs) :
  R.v58120 (state s) (inputs i) = Zmod.unsigned (N.v58120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58120 s i)) at 1.
  unfold R.v58120, N.v58120.
  rewrite ?node_58118.
  rewrite ?node_58119.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58121 (s : N.State) (i : N.Inputs) :
  R.v58121 (state s) (inputs i) = Zmod.unsigned (N.v58121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58121 s i)) at 1.
  unfold R.v58121, N.v58121.
  rewrite ?node_58117.
  rewrite ?node_58120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58122 (s : N.State) (i : N.Inputs) :
  R.v58122 (state s) (inputs i) = Zmod.unsigned (N.v58122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58122 s i)) at 1.
  unfold R.v58122, N.v58122.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58123 (s : N.State) (i : N.Inputs) :
  R.v58123 (state s) (inputs i) = Zmod.unsigned (N.v58123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58123 s i)) at 1.
  unfold R.v58123, N.v58123.
  unfold R.v6, N.v6.
  rewrite ?node_11540.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58124 (s : N.State) (i : N.Inputs) :
  R.v58124 (state s) (inputs i) = Zmod.unsigned (N.v58124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58124 s i)) at 1.
  unfold R.v58124, N.v58124.
  unfold R.v6, N.v6.
  rewrite ?node_11537.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58125 (s : N.State) (i : N.Inputs) :
  R.v58125 (state s) (inputs i) = Zmod.unsigned (N.v58125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58125 s i)) at 1.
  unfold R.v58125, N.v58125.
  rewrite ?node_58123.
  rewrite ?node_58124.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58126 (s : N.State) (i : N.Inputs) :
  R.v58126 (state s) (inputs i) = Zmod.unsigned (N.v58126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58126 s i)) at 1.
  unfold R.v58126, N.v58126.
  unfold R.v16463, N.v16463.
  rewrite ?node_58125.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58127 (s : N.State) (i : N.Inputs) :
  R.v58127 (state s) (inputs i) = Zmod.unsigned (N.v58127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58127 s i)) at 1.
  unfold R.v58127, N.v58127.
  rewrite ?node_11541.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58128 (s : N.State) (i : N.Inputs) :
  R.v58128 (state s) (inputs i) = Zmod.unsigned (N.v58128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58128 s i)) at 1.
  unfold R.v58128, N.v58128.
  unfold R.v6, N.v6.
  rewrite ?node_11692.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58129 (s : N.State) (i : N.Inputs) :
  R.v58129 (state s) (inputs i) = Zmod.unsigned (N.v58129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58129 s i)) at 1.
  unfold R.v58129, N.v58129.
  rewrite ?node_58127.
  rewrite ?node_58128.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58130 (s : N.State) (i : N.Inputs) :
  R.v58130 (state s) (inputs i) = Zmod.unsigned (N.v58130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58130 s i)) at 1.
  unfold R.v58130, N.v58130.
  rewrite ?node_58126.
  rewrite ?node_58129.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58131 (s : N.State) (i : N.Inputs) :
  R.v58131 (state s) (inputs i) = Zmod.unsigned (N.v58131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58131 s i)) at 1.
  unfold R.v58131, N.v58131.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58132 (s : N.State) (i : N.Inputs) :
  R.v58132 (state s) (inputs i) = Zmod.unsigned (N.v58132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58132 s i)) at 1.
  unfold R.v58132, N.v58132.
  unfold R.v6, N.v6.
  rewrite ?node_11689.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58133 (s : N.State) (i : N.Inputs) :
  R.v58133 (state s) (inputs i) = Zmod.unsigned (N.v58133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58133 s i)) at 1.
  unfold R.v58133, N.v58133.
  unfold R.v6, N.v6.
  rewrite ?node_11686.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58134 (s : N.State) (i : N.Inputs) :
  R.v58134 (state s) (inputs i) = Zmod.unsigned (N.v58134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58134 s i)) at 1.
  unfold R.v58134, N.v58134.
  rewrite ?node_58132.
  rewrite ?node_58133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58135 (s : N.State) (i : N.Inputs) :
  R.v58135 (state s) (inputs i) = Zmod.unsigned (N.v58135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58135 s i)) at 1.
  unfold R.v58135, N.v58135.
  unfold R.v16463, N.v16463.
  rewrite ?node_58134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58136 (s : N.State) (i : N.Inputs) :
  R.v58136 (state s) (inputs i) = Zmod.unsigned (N.v58136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58136 s i)) at 1.
  unfold R.v58136, N.v58136.
  rewrite ?node_11690.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58137 (s : N.State) (i : N.Inputs) :
  R.v58137 (state s) (inputs i) = Zmod.unsigned (N.v58137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58137 s i)) at 1.
  unfold R.v58137, N.v58137.
  unfold R.v6, N.v6.
  rewrite ?node_11838.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58138 (s : N.State) (i : N.Inputs) :
  R.v58138 (state s) (inputs i) = Zmod.unsigned (N.v58138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58138 s i)) at 1.
  unfold R.v58138, N.v58138.
  rewrite ?node_58136.
  rewrite ?node_58137.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58139 (s : N.State) (i : N.Inputs) :
  R.v58139 (state s) (inputs i) = Zmod.unsigned (N.v58139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58139 s i)) at 1.
  unfold R.v58139, N.v58139.
  rewrite ?node_58135.
  rewrite ?node_58138.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58140 (s : N.State) (i : N.Inputs) :
  R.v58140 (state s) (inputs i) = Zmod.unsigned (N.v58140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58140 s i)) at 1.
  unfold R.v58140, N.v58140.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58141 (s : N.State) (i : N.Inputs) :
  R.v58141 (state s) (inputs i) = Zmod.unsigned (N.v58141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58141 s i)) at 1.
  unfold R.v58141, N.v58141.
  unfold R.v6, N.v6.
  rewrite ?node_11835.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58142 (s : N.State) (i : N.Inputs) :
  R.v58142 (state s) (inputs i) = Zmod.unsigned (N.v58142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58142 s i)) at 1.
  unfold R.v58142, N.v58142.
  unfold R.v6, N.v6.
  rewrite ?node_11832.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58143 (s : N.State) (i : N.Inputs) :
  R.v58143 (state s) (inputs i) = Zmod.unsigned (N.v58143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58143 s i)) at 1.
  unfold R.v58143, N.v58143.
  rewrite ?node_58141.
  rewrite ?node_58142.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58144 (s : N.State) (i : N.Inputs) :
  R.v58144 (state s) (inputs i) = Zmod.unsigned (N.v58144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58144 s i)) at 1.
  unfold R.v58144, N.v58144.
  unfold R.v16463, N.v16463.
  rewrite ?node_58143.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58145 (s : N.State) (i : N.Inputs) :
  R.v58145 (state s) (inputs i) = Zmod.unsigned (N.v58145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58145 s i)) at 1.
  unfold R.v58145, N.v58145.
  rewrite ?node_11836.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58146 (s : N.State) (i : N.Inputs) :
  R.v58146 (state s) (inputs i) = Zmod.unsigned (N.v58146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58146 s i)) at 1.
  unfold R.v58146, N.v58146.
  unfold R.v6, N.v6.
  rewrite ?node_11982.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58147 (s : N.State) (i : N.Inputs) :
  R.v58147 (state s) (inputs i) = Zmod.unsigned (N.v58147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58147 s i)) at 1.
  unfold R.v58147, N.v58147.
  rewrite ?node_58145.
  rewrite ?node_58146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58148 (s : N.State) (i : N.Inputs) :
  R.v58148 (state s) (inputs i) = Zmod.unsigned (N.v58148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58148 s i)) at 1.
  unfold R.v58148, N.v58148.
  rewrite ?node_58144.
  rewrite ?node_58147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58149 (s : N.State) (i : N.Inputs) :
  R.v58149 (state s) (inputs i) = Zmod.unsigned (N.v58149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58149 s i)) at 1.
  unfold R.v58149, N.v58149.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58150 (s : N.State) (i : N.Inputs) :
  R.v58150 (state s) (inputs i) = Zmod.unsigned (N.v58150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58150 s i)) at 1.
  unfold R.v58150, N.v58150.
  unfold R.v6, N.v6.
  rewrite ?node_11979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58151 (s : N.State) (i : N.Inputs) :
  R.v58151 (state s) (inputs i) = Zmod.unsigned (N.v58151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58151 s i)) at 1.
  unfold R.v58151, N.v58151.
  unfold R.v6, N.v6.
  rewrite ?node_11976.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58152 (s : N.State) (i : N.Inputs) :
  R.v58152 (state s) (inputs i) = Zmod.unsigned (N.v58152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58152 s i)) at 1.
  unfold R.v58152, N.v58152.
  rewrite ?node_58150.
  rewrite ?node_58151.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58153 (s : N.State) (i : N.Inputs) :
  R.v58153 (state s) (inputs i) = Zmod.unsigned (N.v58153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58153 s i)) at 1.
  unfold R.v58153, N.v58153.
  unfold R.v16463, N.v16463.
  rewrite ?node_58152.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58154 (s : N.State) (i : N.Inputs) :
  R.v58154 (state s) (inputs i) = Zmod.unsigned (N.v58154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58154 s i)) at 1.
  unfold R.v58154, N.v58154.
  rewrite ?node_11980.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58155 (s : N.State) (i : N.Inputs) :
  R.v58155 (state s) (inputs i) = Zmod.unsigned (N.v58155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58155 s i)) at 1.
  unfold R.v58155, N.v58155.
  unfold R.v6, N.v6.
  rewrite ?node_12125.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58156 (s : N.State) (i : N.Inputs) :
  R.v58156 (state s) (inputs i) = Zmod.unsigned (N.v58156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58156 s i)) at 1.
  unfold R.v58156, N.v58156.
  rewrite ?node_58154.
  rewrite ?node_58155.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58157 (s : N.State) (i : N.Inputs) :
  R.v58157 (state s) (inputs i) = Zmod.unsigned (N.v58157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58157 s i)) at 1.
  unfold R.v58157, N.v58157.
  rewrite ?node_58153.
  rewrite ?node_58156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58158 (s : N.State) (i : N.Inputs) :
  R.v58158 (state s) (inputs i) = Zmod.unsigned (N.v58158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58158 s i)) at 1.
  unfold R.v58158, N.v58158.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58159 (s : N.State) (i : N.Inputs) :
  R.v58159 (state s) (inputs i) = Zmod.unsigned (N.v58159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58159 s i)) at 1.
  unfold R.v58159, N.v58159.
  rewrite ?node_12122.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58160 (s : N.State) (i : N.Inputs) :
  R.v58160 (state s) (inputs i) = Zmod.unsigned (N.v58160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58160 s i)) at 1.
  unfold R.v58160, N.v58160.
  unfold R.v6, N.v6.
  rewrite ?node_12118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58161 (s : N.State) (i : N.Inputs) :
  R.v58161 (state s) (inputs i) = Zmod.unsigned (N.v58161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58161 s i)) at 1.
  unfold R.v58161, N.v58161.
  unfold R.v6, N.v6.
  rewrite ?node_12115.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58162 (s : N.State) (i : N.Inputs) :
  R.v58162 (state s) (inputs i) = Zmod.unsigned (N.v58162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58162 s i)) at 1.
  unfold R.v58162, N.v58162.
  rewrite ?node_58160.
  rewrite ?node_58161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58163 (s : N.State) (i : N.Inputs) :
  R.v58163 (state s) (inputs i) = Zmod.unsigned (N.v58163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58163 s i)) at 1.
  unfold R.v58163, N.v58163.
  unfold R.v16484, N.v16484.
  rewrite ?node_58162.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58164 (s : N.State) (i : N.Inputs) :
  R.v58164 (state s) (inputs i) = Zmod.unsigned (N.v58164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58164 s i)) at 1.
  unfold R.v58164, N.v58164.
  rewrite ?node_58159.
  rewrite ?node_58163.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58165 (s : N.State) (i : N.Inputs) :
  R.v58165 (state s) (inputs i) = Zmod.unsigned (N.v58165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58165 s i)) at 1.
  unfold R.v58165, N.v58165.
  unfold R.v6, N.v6.
  rewrite ?node_58164.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58166 (s : N.State) (i : N.Inputs) :
  R.v58166 (state s) (inputs i) = Zmod.unsigned (N.v58166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58166 s i)) at 1.
  unfold R.v58166, N.v58166.
  rewrite ?node_12123.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58167 (s : N.State) (i : N.Inputs) :
  R.v58167 (state s) (inputs i) = Zmod.unsigned (N.v58167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58167 s i)) at 1.
  unfold R.v58167, N.v58167.
  unfold R.v6, N.v6.
  rewrite ?node_12264.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58168 (s : N.State) (i : N.Inputs) :
  R.v58168 (state s) (inputs i) = Zmod.unsigned (N.v58168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58168 s i)) at 1.
  unfold R.v58168, N.v58168.
  rewrite ?node_58166.
  rewrite ?node_58167.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58169 (s : N.State) (i : N.Inputs) :
  R.v58169 (state s) (inputs i) = Zmod.unsigned (N.v58169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58169 s i)) at 1.
  unfold R.v58169, N.v58169.
  rewrite ?node_58165.
  rewrite ?node_58168.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58170 (s : N.State) (i : N.Inputs) :
  R.v58170 (state s) (inputs i) = Zmod.unsigned (N.v58170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58170 s i)) at 1.
  unfold R.v58170, N.v58170.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58171 (s : N.State) (i : N.Inputs) :
  R.v58171 (state s) (inputs i) = Zmod.unsigned (N.v58171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58171 s i)) at 1.
  unfold R.v58171, N.v58171.
  unfold R.v6, N.v6.
  rewrite ?node_12259.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58172 (s : N.State) (i : N.Inputs) :
  R.v58172 (state s) (inputs i) = Zmod.unsigned (N.v58172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58172 s i)) at 1.
  unfold R.v58172, N.v58172.
  unfold R.v6, N.v6.
  rewrite ?node_12256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58173 (s : N.State) (i : N.Inputs) :
  R.v58173 (state s) (inputs i) = Zmod.unsigned (N.v58173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58173 s i)) at 1.
  unfold R.v58173, N.v58173.
  rewrite ?node_58171.
  rewrite ?node_58172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58174 (s : N.State) (i : N.Inputs) :
  R.v58174 (state s) (inputs i) = Zmod.unsigned (N.v58174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58174 s i)) at 1.
  unfold R.v58174, N.v58174.
  unfold R.v16463, N.v16463.
  rewrite ?node_58173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58175 (s : N.State) (i : N.Inputs) :
  R.v58175 (state s) (inputs i) = Zmod.unsigned (N.v58175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58175 s i)) at 1.
  unfold R.v58175, N.v58175.
  rewrite ?node_12260.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58176 (s : N.State) (i : N.Inputs) :
  R.v58176 (state s) (inputs i) = Zmod.unsigned (N.v58176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58176 s i)) at 1.
  unfold R.v58176, N.v58176.
  unfold R.v6, N.v6.
  rewrite ?node_12400.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58177 (s : N.State) (i : N.Inputs) :
  R.v58177 (state s) (inputs i) = Zmod.unsigned (N.v58177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58177 s i)) at 1.
  unfold R.v58177, N.v58177.
  rewrite ?node_58175.
  rewrite ?node_58176.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58178 (s : N.State) (i : N.Inputs) :
  R.v58178 (state s) (inputs i) = Zmod.unsigned (N.v58178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58178 s i)) at 1.
  unfold R.v58178, N.v58178.
  rewrite ?node_58174.
  rewrite ?node_58177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58179 (s : N.State) (i : N.Inputs) :
  R.v58179 (state s) (inputs i) = Zmod.unsigned (N.v58179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58179 s i)) at 1.
  unfold R.v58179, N.v58179.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58180 (s : N.State) (i : N.Inputs) :
  R.v58180 (state s) (inputs i) = Zmod.unsigned (N.v58180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58180 s i)) at 1.
  unfold R.v58180, N.v58180.
  unfold R.v6, N.v6.
  rewrite ?node_12397.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58181 (s : N.State) (i : N.Inputs) :
  R.v58181 (state s) (inputs i) = Zmod.unsigned (N.v58181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58181 s i)) at 1.
  unfold R.v58181, N.v58181.
  unfold R.v6, N.v6.
  rewrite ?node_12394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58182 (s : N.State) (i : N.Inputs) :
  R.v58182 (state s) (inputs i) = Zmod.unsigned (N.v58182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58182 s i)) at 1.
  unfold R.v58182, N.v58182.
  rewrite ?node_58180.
  rewrite ?node_58181.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58183 (s : N.State) (i : N.Inputs) :
  R.v58183 (state s) (inputs i) = Zmod.unsigned (N.v58183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58183 s i)) at 1.
  unfold R.v58183, N.v58183.
  unfold R.v16463, N.v16463.
  rewrite ?node_58182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58184 (s : N.State) (i : N.Inputs) :
  R.v58184 (state s) (inputs i) = Zmod.unsigned (N.v58184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58184 s i)) at 1.
  unfold R.v58184, N.v58184.
  rewrite ?node_12398.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58185 (s : N.State) (i : N.Inputs) :
  R.v58185 (state s) (inputs i) = Zmod.unsigned (N.v58185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58185 s i)) at 1.
  unfold R.v58185, N.v58185.
  unfold R.v6, N.v6.
  rewrite ?node_12534.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58186 (s : N.State) (i : N.Inputs) :
  R.v58186 (state s) (inputs i) = Zmod.unsigned (N.v58186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58186 s i)) at 1.
  unfold R.v58186, N.v58186.
  rewrite ?node_58184.
  rewrite ?node_58185.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58187 (s : N.State) (i : N.Inputs) :
  R.v58187 (state s) (inputs i) = Zmod.unsigned (N.v58187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58187 s i)) at 1.
  unfold R.v58187, N.v58187.
  rewrite ?node_58183.
  rewrite ?node_58186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58188 (s : N.State) (i : N.Inputs) :
  R.v58188 (state s) (inputs i) = Zmod.unsigned (N.v58188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58188 s i)) at 1.
  unfold R.v58188, N.v58188.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58189 (s : N.State) (i : N.Inputs) :
  R.v58189 (state s) (inputs i) = Zmod.unsigned (N.v58189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58189 s i)) at 1.
  unfold R.v58189, N.v58189.
  unfold R.v6, N.v6.
  rewrite ?node_12531.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58190 (s : N.State) (i : N.Inputs) :
  R.v58190 (state s) (inputs i) = Zmod.unsigned (N.v58190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58190 s i)) at 1.
  unfold R.v58190, N.v58190.
  unfold R.v6, N.v6.
  rewrite ?node_12528.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58191 (s : N.State) (i : N.Inputs) :
  R.v58191 (state s) (inputs i) = Zmod.unsigned (N.v58191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58191 s i)) at 1.
  unfold R.v58191, N.v58191.
  rewrite ?node_58189.
  rewrite ?node_58190.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58192 (s : N.State) (i : N.Inputs) :
  R.v58192 (state s) (inputs i) = Zmod.unsigned (N.v58192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58192 s i)) at 1.
  unfold R.v58192, N.v58192.
  unfold R.v16463, N.v16463.
  rewrite ?node_58191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58193 (s : N.State) (i : N.Inputs) :
  R.v58193 (state s) (inputs i) = Zmod.unsigned (N.v58193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58193 s i)) at 1.
  unfold R.v58193, N.v58193.
  rewrite ?node_12532.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58194 (s : N.State) (i : N.Inputs) :
  R.v58194 (state s) (inputs i) = Zmod.unsigned (N.v58194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58194 s i)) at 1.
  unfold R.v58194, N.v58194.
  unfold R.v6, N.v6.
  rewrite ?node_12667.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58195 (s : N.State) (i : N.Inputs) :
  R.v58195 (state s) (inputs i) = Zmod.unsigned (N.v58195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58195 s i)) at 1.
  unfold R.v58195, N.v58195.
  rewrite ?node_58193.
  rewrite ?node_58194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58196 (s : N.State) (i : N.Inputs) :
  R.v58196 (state s) (inputs i) = Zmod.unsigned (N.v58196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58196 s i)) at 1.
  unfold R.v58196, N.v58196.
  rewrite ?node_58192.
  rewrite ?node_58195.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58197 (s : N.State) (i : N.Inputs) :
  R.v58197 (state s) (inputs i) = Zmod.unsigned (N.v58197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58197 s i)) at 1.
  unfold R.v58197, N.v58197.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58198 (s : N.State) (i : N.Inputs) :
  R.v58198 (state s) (inputs i) = Zmod.unsigned (N.v58198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58198 s i)) at 1.
  unfold R.v58198, N.v58198.
  unfold R.v6, N.v6.
  rewrite ?node_12664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58199 (s : N.State) (i : N.Inputs) :
  R.v58199 (state s) (inputs i) = Zmod.unsigned (N.v58199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58199 s i)) at 1.
  unfold R.v58199, N.v58199.
  unfold R.v6, N.v6.
  rewrite ?node_12661.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58200 (s : N.State) (i : N.Inputs) :
  R.v58200 (state s) (inputs i) = Zmod.unsigned (N.v58200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58200 s i)) at 1.
  unfold R.v58200, N.v58200.
  rewrite ?node_58198.
  rewrite ?node_58199.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58201 (s : N.State) (i : N.Inputs) :
  R.v58201 (state s) (inputs i) = Zmod.unsigned (N.v58201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58201 s i)) at 1.
  unfold R.v58201, N.v58201.
  unfold R.v16463, N.v16463.
  rewrite ?node_58200.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58202 (s : N.State) (i : N.Inputs) :
  R.v58202 (state s) (inputs i) = Zmod.unsigned (N.v58202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58202 s i)) at 1.
  unfold R.v58202, N.v58202.
  rewrite ?node_12665.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58203 (s : N.State) (i : N.Inputs) :
  R.v58203 (state s) (inputs i) = Zmod.unsigned (N.v58203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58203 s i)) at 1.
  unfold R.v58203, N.v58203.
  unfold R.v6, N.v6.
  rewrite ?node_12796.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58204 (s : N.State) (i : N.Inputs) :
  R.v58204 (state s) (inputs i) = Zmod.unsigned (N.v58204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58204 s i)) at 1.
  unfold R.v58204, N.v58204.
  rewrite ?node_58202.
  rewrite ?node_58203.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58205 (s : N.State) (i : N.Inputs) :
  R.v58205 (state s) (inputs i) = Zmod.unsigned (N.v58205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58205 s i)) at 1.
  unfold R.v58205, N.v58205.
  rewrite ?node_58201.
  rewrite ?node_58204.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58206 (s : N.State) (i : N.Inputs) :
  R.v58206 (state s) (inputs i) = Zmod.unsigned (N.v58206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58206 s i)) at 1.
  unfold R.v58206, N.v58206.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58207 (s : N.State) (i : N.Inputs) :
  R.v58207 (state s) (inputs i) = Zmod.unsigned (N.v58207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58207 s i)) at 1.
  unfold R.v58207, N.v58207.
  unfold R.v6, N.v6.
  rewrite ?node_12793.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58208 (s : N.State) (i : N.Inputs) :
  R.v58208 (state s) (inputs i) = Zmod.unsigned (N.v58208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58208 s i)) at 1.
  unfold R.v58208, N.v58208.
  unfold R.v6, N.v6.
  rewrite ?node_12790.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58209 (s : N.State) (i : N.Inputs) :
  R.v58209 (state s) (inputs i) = Zmod.unsigned (N.v58209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58209 s i)) at 1.
  unfold R.v58209, N.v58209.
  rewrite ?node_58207.
  rewrite ?node_58208.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58210 (s : N.State) (i : N.Inputs) :
  R.v58210 (state s) (inputs i) = Zmod.unsigned (N.v58210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58210 s i)) at 1.
  unfold R.v58210, N.v58210.
  unfold R.v16463, N.v16463.
  rewrite ?node_58209.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58211 (s : N.State) (i : N.Inputs) :
  R.v58211 (state s) (inputs i) = Zmod.unsigned (N.v58211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58211 s i)) at 1.
  unfold R.v58211, N.v58211.
  rewrite ?node_12794.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58212 (s : N.State) (i : N.Inputs) :
  R.v58212 (state s) (inputs i) = Zmod.unsigned (N.v58212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58212 s i)) at 1.
  unfold R.v58212, N.v58212.
  unfold R.v6, N.v6.
  rewrite ?node_12924.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58213 (s : N.State) (i : N.Inputs) :
  R.v58213 (state s) (inputs i) = Zmod.unsigned (N.v58213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58213 s i)) at 1.
  unfold R.v58213, N.v58213.
  rewrite ?node_58211.
  rewrite ?node_58212.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58214 (s : N.State) (i : N.Inputs) :
  R.v58214 (state s) (inputs i) = Zmod.unsigned (N.v58214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58214 s i)) at 1.
  unfold R.v58214, N.v58214.
  rewrite ?node_58210.
  rewrite ?node_58213.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58215 (s : N.State) (i : N.Inputs) :
  R.v58215 (state s) (inputs i) = Zmod.unsigned (N.v58215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58215 s i)) at 1.
  unfold R.v58215, N.v58215.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58216 (s : N.State) (i : N.Inputs) :
  R.v58216 (state s) (inputs i) = Zmod.unsigned (N.v58216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58216 s i)) at 1.
  unfold R.v58216, N.v58216.
  unfold R.v6, N.v6.
  rewrite ?node_12921.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58217 (s : N.State) (i : N.Inputs) :
  R.v58217 (state s) (inputs i) = Zmod.unsigned (N.v58217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58217 s i)) at 1.
  unfold R.v58217, N.v58217.
  unfold R.v6, N.v6.
  rewrite ?node_12918.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58218 (s : N.State) (i : N.Inputs) :
  R.v58218 (state s) (inputs i) = Zmod.unsigned (N.v58218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58218 s i)) at 1.
  unfold R.v58218, N.v58218.
  rewrite ?node_58216.
  rewrite ?node_58217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58219 (s : N.State) (i : N.Inputs) :
  R.v58219 (state s) (inputs i) = Zmod.unsigned (N.v58219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58219 s i)) at 1.
  unfold R.v58219, N.v58219.
  unfold R.v16463, N.v16463.
  rewrite ?node_58218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58220 (s : N.State) (i : N.Inputs) :
  R.v58220 (state s) (inputs i) = Zmod.unsigned (N.v58220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58220 s i)) at 1.
  unfold R.v58220, N.v58220.
  rewrite ?node_12922.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58221 (s : N.State) (i : N.Inputs) :
  R.v58221 (state s) (inputs i) = Zmod.unsigned (N.v58221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58221 s i)) at 1.
  unfold R.v58221, N.v58221.
  unfold R.v6, N.v6.
  rewrite ?node_13050.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58222 (s : N.State) (i : N.Inputs) :
  R.v58222 (state s) (inputs i) = Zmod.unsigned (N.v58222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58222 s i)) at 1.
  unfold R.v58222, N.v58222.
  rewrite ?node_58220.
  rewrite ?node_58221.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58223 (s : N.State) (i : N.Inputs) :
  R.v58223 (state s) (inputs i) = Zmod.unsigned (N.v58223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58223 s i)) at 1.
  unfold R.v58223, N.v58223.
  rewrite ?node_58219.
  rewrite ?node_58222.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58224 (s : N.State) (i : N.Inputs) :
  R.v58224 (state s) (inputs i) = Zmod.unsigned (N.v58224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58224 s i)) at 1.
  unfold R.v58224, N.v58224.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58225 (s : N.State) (i : N.Inputs) :
  R.v58225 (state s) (inputs i) = Zmod.unsigned (N.v58225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58225 s i)) at 1.
  unfold R.v58225, N.v58225.
  unfold R.v6, N.v6.
  rewrite ?node_13047.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58226 (s : N.State) (i : N.Inputs) :
  R.v58226 (state s) (inputs i) = Zmod.unsigned (N.v58226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58226 s i)) at 1.
  unfold R.v58226, N.v58226.
  unfold R.v6, N.v6.
  rewrite ?node_13044.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58227 (s : N.State) (i : N.Inputs) :
  R.v58227 (state s) (inputs i) = Zmod.unsigned (N.v58227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58227 s i)) at 1.
  unfold R.v58227, N.v58227.
  rewrite ?node_58225.
  rewrite ?node_58226.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58228 (s : N.State) (i : N.Inputs) :
  R.v58228 (state s) (inputs i) = Zmod.unsigned (N.v58228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58228 s i)) at 1.
  unfold R.v58228, N.v58228.
  unfold R.v16463, N.v16463.
  rewrite ?node_58227.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58229 (s : N.State) (i : N.Inputs) :
  R.v58229 (state s) (inputs i) = Zmod.unsigned (N.v58229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58229 s i)) at 1.
  unfold R.v58229, N.v58229.
  rewrite ?node_13048.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58230 (s : N.State) (i : N.Inputs) :
  R.v58230 (state s) (inputs i) = Zmod.unsigned (N.v58230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58230 s i)) at 1.
  unfold R.v58230, N.v58230.
  unfold R.v6, N.v6.
  rewrite ?node_13175.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58231 (s : N.State) (i : N.Inputs) :
  R.v58231 (state s) (inputs i) = Zmod.unsigned (N.v58231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58231 s i)) at 1.
  unfold R.v58231, N.v58231.
  rewrite ?node_58229.
  rewrite ?node_58230.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58232 (s : N.State) (i : N.Inputs) :
  R.v58232 (state s) (inputs i) = Zmod.unsigned (N.v58232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58232 s i)) at 1.
  unfold R.v58232, N.v58232.
  rewrite ?node_58228.
  rewrite ?node_58231.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58233 (s : N.State) (i : N.Inputs) :
  R.v58233 (state s) (inputs i) = Zmod.unsigned (N.v58233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58233 s i)) at 1.
  unfold R.v58233, N.v58233.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58234 (s : N.State) (i : N.Inputs) :
  R.v58234 (state s) (inputs i) = Zmod.unsigned (N.v58234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58234 s i)) at 1.
  unfold R.v58234, N.v58234.
  unfold R.v6, N.v6.
  rewrite ?node_13172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58235 (s : N.State) (i : N.Inputs) :
  R.v58235 (state s) (inputs i) = Zmod.unsigned (N.v58235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58235 s i)) at 1.
  unfold R.v58235, N.v58235.
  unfold R.v6, N.v6.
  rewrite ?node_13169.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58236 (s : N.State) (i : N.Inputs) :
  R.v58236 (state s) (inputs i) = Zmod.unsigned (N.v58236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58236 s i)) at 1.
  unfold R.v58236, N.v58236.
  rewrite ?node_58234.
  rewrite ?node_58235.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58237 (s : N.State) (i : N.Inputs) :
  R.v58237 (state s) (inputs i) = Zmod.unsigned (N.v58237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58237 s i)) at 1.
  unfold R.v58237, N.v58237.
  unfold R.v16463, N.v16463.
  rewrite ?node_58236.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58238 (s : N.State) (i : N.Inputs) :
  R.v58238 (state s) (inputs i) = Zmod.unsigned (N.v58238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58238 s i)) at 1.
  unfold R.v58238, N.v58238.
  rewrite ?node_13173.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58239 (s : N.State) (i : N.Inputs) :
  R.v58239 (state s) (inputs i) = Zmod.unsigned (N.v58239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58239 s i)) at 1.
  unfold R.v58239, N.v58239.
  unfold R.v6, N.v6.
  rewrite ?node_13296.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58240 (s : N.State) (i : N.Inputs) :
  R.v58240 (state s) (inputs i) = Zmod.unsigned (N.v58240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58240 s i)) at 1.
  unfold R.v58240, N.v58240.
  rewrite ?node_58238.
  rewrite ?node_58239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58241 (s : N.State) (i : N.Inputs) :
  R.v58241 (state s) (inputs i) = Zmod.unsigned (N.v58241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58241 s i)) at 1.
  unfold R.v58241, N.v58241.
  rewrite ?node_58237.
  rewrite ?node_58240.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58242 (s : N.State) (i : N.Inputs) :
  R.v58242 (state s) (inputs i) = Zmod.unsigned (N.v58242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58242 s i)) at 1.
  unfold R.v58242, N.v58242.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58243 (s : N.State) (i : N.Inputs) :
  R.v58243 (state s) (inputs i) = Zmod.unsigned (N.v58243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58243 s i)) at 1.
  unfold R.v58243, N.v58243.
  rewrite ?node_13293.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58244 (s : N.State) (i : N.Inputs) :
  R.v58244 (state s) (inputs i) = Zmod.unsigned (N.v58244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58244 s i)) at 1.
  unfold R.v58244, N.v58244.
  unfold R.v6, N.v6.
  rewrite ?node_13289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58245 (s : N.State) (i : N.Inputs) :
  R.v58245 (state s) (inputs i) = Zmod.unsigned (N.v58245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58245 s i)) at 1.
  unfold R.v58245, N.v58245.
  unfold R.v6, N.v6.
  rewrite ?node_13286.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58246 (s : N.State) (i : N.Inputs) :
  R.v58246 (state s) (inputs i) = Zmod.unsigned (N.v58246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58246 s i)) at 1.
  unfold R.v58246, N.v58246.
  rewrite ?node_58244.
  rewrite ?node_58245.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58247 (s : N.State) (i : N.Inputs) :
  R.v58247 (state s) (inputs i) = Zmod.unsigned (N.v58247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58247 s i)) at 1.
  unfold R.v58247, N.v58247.
  unfold R.v16484, N.v16484.
  rewrite ?node_58246.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58248 (s : N.State) (i : N.Inputs) :
  R.v58248 (state s) (inputs i) = Zmod.unsigned (N.v58248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58248 s i)) at 1.
  unfold R.v58248, N.v58248.
  rewrite ?node_58243.
  rewrite ?node_58247.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58249 (s : N.State) (i : N.Inputs) :
  R.v58249 (state s) (inputs i) = Zmod.unsigned (N.v58249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58249 s i)) at 1.
  unfold R.v58249, N.v58249.
  unfold R.v6, N.v6.
  rewrite ?node_58248.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58250 (s : N.State) (i : N.Inputs) :
  R.v58250 (state s) (inputs i) = Zmod.unsigned (N.v58250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58250 s i)) at 1.
  unfold R.v58250, N.v58250.
  rewrite ?node_13294.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58251 (s : N.State) (i : N.Inputs) :
  R.v58251 (state s) (inputs i) = Zmod.unsigned (N.v58251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58251 s i)) at 1.
  unfold R.v58251, N.v58251.
  unfold R.v6, N.v6.
  rewrite ?node_13414.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58252 (s : N.State) (i : N.Inputs) :
  R.v58252 (state s) (inputs i) = Zmod.unsigned (N.v58252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58252 s i)) at 1.
  unfold R.v58252, N.v58252.
  rewrite ?node_58250.
  rewrite ?node_58251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58253 (s : N.State) (i : N.Inputs) :
  R.v58253 (state s) (inputs i) = Zmod.unsigned (N.v58253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58253 s i)) at 1.
  unfold R.v58253, N.v58253.
  rewrite ?node_58249.
  rewrite ?node_58252.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58254 (s : N.State) (i : N.Inputs) :
  R.v58254 (state s) (inputs i) = Zmod.unsigned (N.v58254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58254 s i)) at 1.
  unfold R.v58254, N.v58254.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58255 (s : N.State) (i : N.Inputs) :
  R.v58255 (state s) (inputs i) = Zmod.unsigned (N.v58255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58255 s i)) at 1.
  unfold R.v58255, N.v58255.
  unfold R.v6, N.v6.
  rewrite ?node_13409.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58256 (s : N.State) (i : N.Inputs) :
  R.v58256 (state s) (inputs i) = Zmod.unsigned (N.v58256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58256 s i)) at 1.
  unfold R.v58256, N.v58256.
  unfold R.v6, N.v6.
  rewrite ?node_13406.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58257 (s : N.State) (i : N.Inputs) :
  R.v58257 (state s) (inputs i) = Zmod.unsigned (N.v58257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58257 s i)) at 1.
  unfold R.v58257, N.v58257.
  rewrite ?node_58255.
  rewrite ?node_58256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58258 (s : N.State) (i : N.Inputs) :
  R.v58258 (state s) (inputs i) = Zmod.unsigned (N.v58258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58258 s i)) at 1.
  unfold R.v58258, N.v58258.
  unfold R.v16463, N.v16463.
  rewrite ?node_58257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58259 (s : N.State) (i : N.Inputs) :
  R.v58259 (state s) (inputs i) = Zmod.unsigned (N.v58259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58259 s i)) at 1.
  unfold R.v58259, N.v58259.
  rewrite ?node_13410.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58260 (s : N.State) (i : N.Inputs) :
  R.v58260 (state s) (inputs i) = Zmod.unsigned (N.v58260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58260 s i)) at 1.
  unfold R.v58260, N.v58260.
  unfold R.v6, N.v6.
  rewrite ?node_13528.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58261 (s : N.State) (i : N.Inputs) :
  R.v58261 (state s) (inputs i) = Zmod.unsigned (N.v58261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58261 s i)) at 1.
  unfold R.v58261, N.v58261.
  rewrite ?node_58259.
  rewrite ?node_58260.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58262 (s : N.State) (i : N.Inputs) :
  R.v58262 (state s) (inputs i) = Zmod.unsigned (N.v58262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58262 s i)) at 1.
  unfold R.v58262, N.v58262.
  rewrite ?node_58258.
  rewrite ?node_58261.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58263 (s : N.State) (i : N.Inputs) :
  R.v58263 (state s) (inputs i) = Zmod.unsigned (N.v58263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58263 s i)) at 1.
  unfold R.v58263, N.v58263.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58264 (s : N.State) (i : N.Inputs) :
  R.v58264 (state s) (inputs i) = Zmod.unsigned (N.v58264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58264 s i)) at 1.
  unfold R.v58264, N.v58264.
  unfold R.v6, N.v6.
  rewrite ?node_13525.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58265 (s : N.State) (i : N.Inputs) :
  R.v58265 (state s) (inputs i) = Zmod.unsigned (N.v58265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58265 s i)) at 1.
  unfold R.v58265, N.v58265.
  unfold R.v6, N.v6.
  rewrite ?node_13522.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58266 (s : N.State) (i : N.Inputs) :
  R.v58266 (state s) (inputs i) = Zmod.unsigned (N.v58266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58266 s i)) at 1.
  unfold R.v58266, N.v58266.
  rewrite ?node_58264.
  rewrite ?node_58265.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58267 (s : N.State) (i : N.Inputs) :
  R.v58267 (state s) (inputs i) = Zmod.unsigned (N.v58267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58267 s i)) at 1.
  unfold R.v58267, N.v58267.
  unfold R.v16463, N.v16463.
  rewrite ?node_58266.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58268 (s : N.State) (i : N.Inputs) :
  R.v58268 (state s) (inputs i) = Zmod.unsigned (N.v58268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58268 s i)) at 1.
  unfold R.v58268, N.v58268.
  rewrite ?node_13526.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58269 (s : N.State) (i : N.Inputs) :
  R.v58269 (state s) (inputs i) = Zmod.unsigned (N.v58269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58269 s i)) at 1.
  unfold R.v58269, N.v58269.
  unfold R.v6, N.v6.
  rewrite ?node_13641.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58270 (s : N.State) (i : N.Inputs) :
  R.v58270 (state s) (inputs i) = Zmod.unsigned (N.v58270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58270 s i)) at 1.
  unfold R.v58270, N.v58270.
  rewrite ?node_58268.
  rewrite ?node_58269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58271 (s : N.State) (i : N.Inputs) :
  R.v58271 (state s) (inputs i) = Zmod.unsigned (N.v58271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58271 s i)) at 1.
  unfold R.v58271, N.v58271.
  rewrite ?node_58267.
  rewrite ?node_58270.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58272 (s : N.State) (i : N.Inputs) :
  R.v58272 (state s) (inputs i) = Zmod.unsigned (N.v58272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58272 s i)) at 1.
  unfold R.v58272, N.v58272.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58273 (s : N.State) (i : N.Inputs) :
  R.v58273 (state s) (inputs i) = Zmod.unsigned (N.v58273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58273 s i)) at 1.
  unfold R.v58273, N.v58273.
  unfold R.v6, N.v6.
  rewrite ?node_13638.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58274 (s : N.State) (i : N.Inputs) :
  R.v58274 (state s) (inputs i) = Zmod.unsigned (N.v58274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58274 s i)) at 1.
  unfold R.v58274, N.v58274.
  unfold R.v6, N.v6.
  rewrite ?node_13635.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58275 (s : N.State) (i : N.Inputs) :
  R.v58275 (state s) (inputs i) = Zmod.unsigned (N.v58275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58275 s i)) at 1.
  unfold R.v58275, N.v58275.
  rewrite ?node_58273.
  rewrite ?node_58274.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58276 (s : N.State) (i : N.Inputs) :
  R.v58276 (state s) (inputs i) = Zmod.unsigned (N.v58276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58276 s i)) at 1.
  unfold R.v58276, N.v58276.
  unfold R.v16463, N.v16463.
  rewrite ?node_58275.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58277 (s : N.State) (i : N.Inputs) :
  R.v58277 (state s) (inputs i) = Zmod.unsigned (N.v58277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58277 s i)) at 1.
  unfold R.v58277, N.v58277.
  rewrite ?node_13639.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58278 (s : N.State) (i : N.Inputs) :
  R.v58278 (state s) (inputs i) = Zmod.unsigned (N.v58278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58278 s i)) at 1.
  unfold R.v58278, N.v58278.
  unfold R.v6, N.v6.
  rewrite ?node_13750.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58279 (s : N.State) (i : N.Inputs) :
  R.v58279 (state s) (inputs i) = Zmod.unsigned (N.v58279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58279 s i)) at 1.
  unfold R.v58279, N.v58279.
  rewrite ?node_58277.
  rewrite ?node_58278.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58280 (s : N.State) (i : N.Inputs) :
  R.v58280 (state s) (inputs i) = Zmod.unsigned (N.v58280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58280 s i)) at 1.
  unfold R.v58280, N.v58280.
  rewrite ?node_58276.
  rewrite ?node_58279.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58281 (s : N.State) (i : N.Inputs) :
  R.v58281 (state s) (inputs i) = Zmod.unsigned (N.v58281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58281 s i)) at 1.
  unfold R.v58281, N.v58281.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58282 (s : N.State) (i : N.Inputs) :
  R.v58282 (state s) (inputs i) = Zmod.unsigned (N.v58282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58282 s i)) at 1.
  unfold R.v58282, N.v58282.
  unfold R.v6, N.v6.
  rewrite ?node_13747.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58283 (s : N.State) (i : N.Inputs) :
  R.v58283 (state s) (inputs i) = Zmod.unsigned (N.v58283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58283 s i)) at 1.
  unfold R.v58283, N.v58283.
  unfold R.v6, N.v6.
  rewrite ?node_13744.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58284 (s : N.State) (i : N.Inputs) :
  R.v58284 (state s) (inputs i) = Zmod.unsigned (N.v58284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58284 s i)) at 1.
  unfold R.v58284, N.v58284.
  rewrite ?node_58282.
  rewrite ?node_58283.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58285 (s : N.State) (i : N.Inputs) :
  R.v58285 (state s) (inputs i) = Zmod.unsigned (N.v58285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58285 s i)) at 1.
  unfold R.v58285, N.v58285.
  unfold R.v16463, N.v16463.
  rewrite ?node_58284.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58286 (s : N.State) (i : N.Inputs) :
  R.v58286 (state s) (inputs i) = Zmod.unsigned (N.v58286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58286 s i)) at 1.
  unfold R.v58286, N.v58286.
  rewrite ?node_13748.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58287 (s : N.State) (i : N.Inputs) :
  R.v58287 (state s) (inputs i) = Zmod.unsigned (N.v58287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58287 s i)) at 1.
  unfold R.v58287, N.v58287.
  unfold R.v6, N.v6.
  rewrite ?node_13858.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58288 (s : N.State) (i : N.Inputs) :
  R.v58288 (state s) (inputs i) = Zmod.unsigned (N.v58288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58288 s i)) at 1.
  unfold R.v58288, N.v58288.
  rewrite ?node_58286.
  rewrite ?node_58287.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58289 (s : N.State) (i : N.Inputs) :
  R.v58289 (state s) (inputs i) = Zmod.unsigned (N.v58289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58289 s i)) at 1.
  unfold R.v58289, N.v58289.
  rewrite ?node_58285.
  rewrite ?node_58288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58290 (s : N.State) (i : N.Inputs) :
  R.v58290 (state s) (inputs i) = Zmod.unsigned (N.v58290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58290 s i)) at 1.
  unfold R.v58290, N.v58290.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58291 (s : N.State) (i : N.Inputs) :
  R.v58291 (state s) (inputs i) = Zmod.unsigned (N.v58291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58291 s i)) at 1.
  unfold R.v58291, N.v58291.
  unfold R.v6, N.v6.
  rewrite ?node_13855.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58292 (s : N.State) (i : N.Inputs) :
  R.v58292 (state s) (inputs i) = Zmod.unsigned (N.v58292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58292 s i)) at 1.
  unfold R.v58292, N.v58292.
  unfold R.v6, N.v6.
  rewrite ?node_13852.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58293 (s : N.State) (i : N.Inputs) :
  R.v58293 (state s) (inputs i) = Zmod.unsigned (N.v58293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58293 s i)) at 1.
  unfold R.v58293, N.v58293.
  rewrite ?node_58291.
  rewrite ?node_58292.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58294 (s : N.State) (i : N.Inputs) :
  R.v58294 (state s) (inputs i) = Zmod.unsigned (N.v58294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58294 s i)) at 1.
  unfold R.v58294, N.v58294.
  unfold R.v16463, N.v16463.
  rewrite ?node_58293.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58295 (s : N.State) (i : N.Inputs) :
  R.v58295 (state s) (inputs i) = Zmod.unsigned (N.v58295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58295 s i)) at 1.
  unfold R.v58295, N.v58295.
  rewrite ?node_13856.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58296 (s : N.State) (i : N.Inputs) :
  R.v58296 (state s) (inputs i) = Zmod.unsigned (N.v58296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58296 s i)) at 1.
  unfold R.v58296, N.v58296.
  unfold R.v6, N.v6.
  rewrite ?node_13964.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58297 (s : N.State) (i : N.Inputs) :
  R.v58297 (state s) (inputs i) = Zmod.unsigned (N.v58297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58297 s i)) at 1.
  unfold R.v58297, N.v58297.
  rewrite ?node_58295.
  rewrite ?node_58296.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58298 (s : N.State) (i : N.Inputs) :
  R.v58298 (state s) (inputs i) = Zmod.unsigned (N.v58298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58298 s i)) at 1.
  unfold R.v58298, N.v58298.
  rewrite ?node_58294.
  rewrite ?node_58297.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58299 (s : N.State) (i : N.Inputs) :
  R.v58299 (state s) (inputs i) = Zmod.unsigned (N.v58299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58299 s i)) at 1.
  unfold R.v58299, N.v58299.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58300 (s : N.State) (i : N.Inputs) :
  R.v58300 (state s) (inputs i) = Zmod.unsigned (N.v58300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58300 s i)) at 1.
  unfold R.v58300, N.v58300.
  unfold R.v6, N.v6.
  rewrite ?node_13961.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58301 (s : N.State) (i : N.Inputs) :
  R.v58301 (state s) (inputs i) = Zmod.unsigned (N.v58301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58301 s i)) at 1.
  unfold R.v58301, N.v58301.
  unfold R.v6, N.v6.
  rewrite ?node_13958.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58302 (s : N.State) (i : N.Inputs) :
  R.v58302 (state s) (inputs i) = Zmod.unsigned (N.v58302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58302 s i)) at 1.
  unfold R.v58302, N.v58302.
  rewrite ?node_58300.
  rewrite ?node_58301.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58303 (s : N.State) (i : N.Inputs) :
  R.v58303 (state s) (inputs i) = Zmod.unsigned (N.v58303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58303 s i)) at 1.
  unfold R.v58303, N.v58303.
  unfold R.v16463, N.v16463.
  rewrite ?node_58302.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58304 (s : N.State) (i : N.Inputs) :
  R.v58304 (state s) (inputs i) = Zmod.unsigned (N.v58304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58304 s i)) at 1.
  unfold R.v58304, N.v58304.
  rewrite ?node_13962.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58305 (s : N.State) (i : N.Inputs) :
  R.v58305 (state s) (inputs i) = Zmod.unsigned (N.v58305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58305 s i)) at 1.
  unfold R.v58305, N.v58305.
  unfold R.v6, N.v6.
  rewrite ?node_14069.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58306 (s : N.State) (i : N.Inputs) :
  R.v58306 (state s) (inputs i) = Zmod.unsigned (N.v58306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58306 s i)) at 1.
  unfold R.v58306, N.v58306.
  rewrite ?node_58304.
  rewrite ?node_58305.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58307 (s : N.State) (i : N.Inputs) :
  R.v58307 (state s) (inputs i) = Zmod.unsigned (N.v58307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58307 s i)) at 1.
  unfold R.v58307, N.v58307.
  rewrite ?node_58303.
  rewrite ?node_58306.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58308 (s : N.State) (i : N.Inputs) :
  R.v58308 (state s) (inputs i) = Zmod.unsigned (N.v58308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58308 s i)) at 1.
  unfold R.v58308, N.v58308.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58309 (s : N.State) (i : N.Inputs) :
  R.v58309 (state s) (inputs i) = Zmod.unsigned (N.v58309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58309 s i)) at 1.
  unfold R.v58309, N.v58309.
  unfold R.v6, N.v6.
  rewrite ?node_14066.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58310 (s : N.State) (i : N.Inputs) :
  R.v58310 (state s) (inputs i) = Zmod.unsigned (N.v58310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58310 s i)) at 1.
  unfold R.v58310, N.v58310.
  unfold R.v6, N.v6.
  rewrite ?node_14063.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58311 (s : N.State) (i : N.Inputs) :
  R.v58311 (state s) (inputs i) = Zmod.unsigned (N.v58311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58311 s i)) at 1.
  unfold R.v58311, N.v58311.
  rewrite ?node_58309.
  rewrite ?node_58310.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58312 (s : N.State) (i : N.Inputs) :
  R.v58312 (state s) (inputs i) = Zmod.unsigned (N.v58312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58312 s i)) at 1.
  unfold R.v58312, N.v58312.
  unfold R.v16463, N.v16463.
  rewrite ?node_58311.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58313 (s : N.State) (i : N.Inputs) :
  R.v58313 (state s) (inputs i) = Zmod.unsigned (N.v58313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58313 s i)) at 1.
  unfold R.v58313, N.v58313.
  rewrite ?node_14067.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58314 (s : N.State) (i : N.Inputs) :
  R.v58314 (state s) (inputs i) = Zmod.unsigned (N.v58314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58314 s i)) at 1.
  unfold R.v58314, N.v58314.
  unfold R.v6, N.v6.
  rewrite ?node_14170.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58315 (s : N.State) (i : N.Inputs) :
  R.v58315 (state s) (inputs i) = Zmod.unsigned (N.v58315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58315 s i)) at 1.
  unfold R.v58315, N.v58315.
  rewrite ?node_58313.
  rewrite ?node_58314.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58316 (s : N.State) (i : N.Inputs) :
  R.v58316 (state s) (inputs i) = Zmod.unsigned (N.v58316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58316 s i)) at 1.
  unfold R.v58316, N.v58316.
  rewrite ?node_58312.
  rewrite ?node_58315.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58317 (s : N.State) (i : N.Inputs) :
  R.v58317 (state s) (inputs i) = Zmod.unsigned (N.v58317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58317 s i)) at 1.
  unfold R.v58317, N.v58317.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58318 (s : N.State) (i : N.Inputs) :
  R.v58318 (state s) (inputs i) = Zmod.unsigned (N.v58318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58318 s i)) at 1.
  unfold R.v58318, N.v58318.
  unfold R.v6, N.v6.
  rewrite ?node_14167.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58319 (s : N.State) (i : N.Inputs) :
  R.v58319 (state s) (inputs i) = Zmod.unsigned (N.v58319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58319 s i)) at 1.
  unfold R.v58319, N.v58319.
  unfold R.v6, N.v6.
  rewrite ?node_14164.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58320 (s : N.State) (i : N.Inputs) :
  R.v58320 (state s) (inputs i) = Zmod.unsigned (N.v58320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58320 s i)) at 1.
  unfold R.v58320, N.v58320.
  rewrite ?node_58318.
  rewrite ?node_58319.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58321 (s : N.State) (i : N.Inputs) :
  R.v58321 (state s) (inputs i) = Zmod.unsigned (N.v58321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58321 s i)) at 1.
  unfold R.v58321, N.v58321.
  unfold R.v16463, N.v16463.
  rewrite ?node_58320.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58322 (s : N.State) (i : N.Inputs) :
  R.v58322 (state s) (inputs i) = Zmod.unsigned (N.v58322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58322 s i)) at 1.
  unfold R.v58322, N.v58322.
  rewrite ?node_14168.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58323 (s : N.State) (i : N.Inputs) :
  R.v58323 (state s) (inputs i) = Zmod.unsigned (N.v58323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58323 s i)) at 1.
  unfold R.v58323, N.v58323.
  unfold R.v6, N.v6.
  rewrite ?node_14268.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58324 (s : N.State) (i : N.Inputs) :
  R.v58324 (state s) (inputs i) = Zmod.unsigned (N.v58324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58324 s i)) at 1.
  unfold R.v58324, N.v58324.
  rewrite ?node_58322.
  rewrite ?node_58323.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58325 (s : N.State) (i : N.Inputs) :
  R.v58325 (state s) (inputs i) = Zmod.unsigned (N.v58325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58325 s i)) at 1.
  unfold R.v58325, N.v58325.
  rewrite ?node_58321.
  rewrite ?node_58324.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58326 (s : N.State) (i : N.Inputs) :
  R.v58326 (state s) (inputs i) = Zmod.unsigned (N.v58326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58326 s i)) at 1.
  unfold R.v58326, N.v58326.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58327 (s : N.State) (i : N.Inputs) :
  R.v58327 (state s) (inputs i) = Zmod.unsigned (N.v58327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58327 s i)) at 1.
  unfold R.v58327, N.v58327.
  unfold R.v6, N.v6.
  rewrite ?node_14265.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58328 (s : N.State) (i : N.Inputs) :
  R.v58328 (state s) (inputs i) = Zmod.unsigned (N.v58328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58328 s i)) at 1.
  unfold R.v58328, N.v58328.
  unfold R.v6, N.v6.
  rewrite ?node_14262.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58329 (s : N.State) (i : N.Inputs) :
  R.v58329 (state s) (inputs i) = Zmod.unsigned (N.v58329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58329 s i)) at 1.
  unfold R.v58329, N.v58329.
  rewrite ?node_58327.
  rewrite ?node_58328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58330 (s : N.State) (i : N.Inputs) :
  R.v58330 (state s) (inputs i) = Zmod.unsigned (N.v58330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58330 s i)) at 1.
  unfold R.v58330, N.v58330.
  unfold R.v16463, N.v16463.
  rewrite ?node_58329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58331 (s : N.State) (i : N.Inputs) :
  R.v58331 (state s) (inputs i) = Zmod.unsigned (N.v58331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58331 s i)) at 1.
  unfold R.v58331, N.v58331.
  rewrite ?node_14266.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58332 (s : N.State) (i : N.Inputs) :
  R.v58332 (state s) (inputs i) = Zmod.unsigned (N.v58332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58332 s i)) at 1.
  unfold R.v58332, N.v58332.
  unfold R.v6, N.v6.
  rewrite ?node_14364.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58333 (s : N.State) (i : N.Inputs) :
  R.v58333 (state s) (inputs i) = Zmod.unsigned (N.v58333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58333 s i)) at 1.
  unfold R.v58333, N.v58333.
  rewrite ?node_58331.
  rewrite ?node_58332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58334 (s : N.State) (i : N.Inputs) :
  R.v58334 (state s) (inputs i) = Zmod.unsigned (N.v58334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58334 s i)) at 1.
  unfold R.v58334, N.v58334.
  rewrite ?node_58330.
  rewrite ?node_58333.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58335 (s : N.State) (i : N.Inputs) :
  R.v58335 (state s) (inputs i) = Zmod.unsigned (N.v58335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58335 s i)) at 1.
  unfold R.v58335, N.v58335.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58336 (s : N.State) (i : N.Inputs) :
  R.v58336 (state s) (inputs i) = Zmod.unsigned (N.v58336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58336 s i)) at 1.
  unfold R.v58336, N.v58336.
  unfold R.v6, N.v6.
  rewrite ?node_14361.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58337 (s : N.State) (i : N.Inputs) :
  R.v58337 (state s) (inputs i) = Zmod.unsigned (N.v58337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58337 s i)) at 1.
  unfold R.v58337, N.v58337.
  unfold R.v6, N.v6.
  rewrite ?node_14358.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58338 (s : N.State) (i : N.Inputs) :
  R.v58338 (state s) (inputs i) = Zmod.unsigned (N.v58338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58338 s i)) at 1.
  unfold R.v58338, N.v58338.
  rewrite ?node_58336.
  rewrite ?node_58337.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58339 (s : N.State) (i : N.Inputs) :
  R.v58339 (state s) (inputs i) = Zmod.unsigned (N.v58339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58339 s i)) at 1.
  unfold R.v58339, N.v58339.
  unfold R.v16463, N.v16463.
  rewrite ?node_58338.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58340 (s : N.State) (i : N.Inputs) :
  R.v58340 (state s) (inputs i) = Zmod.unsigned (N.v58340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58340 s i)) at 1.
  unfold R.v58340, N.v58340.
  rewrite ?node_14362.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58341 (s : N.State) (i : N.Inputs) :
  R.v58341 (state s) (inputs i) = Zmod.unsigned (N.v58341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58341 s i)) at 1.
  unfold R.v58341, N.v58341.
  unfold R.v6, N.v6.
  rewrite ?node_14459.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58342 (s : N.State) (i : N.Inputs) :
  R.v58342 (state s) (inputs i) = Zmod.unsigned (N.v58342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58342 s i)) at 1.
  unfold R.v58342, N.v58342.
  rewrite ?node_58340.
  rewrite ?node_58341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58343 (s : N.State) (i : N.Inputs) :
  R.v58343 (state s) (inputs i) = Zmod.unsigned (N.v58343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58343 s i)) at 1.
  unfold R.v58343, N.v58343.
  rewrite ?node_58339.
  rewrite ?node_58342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58344 (s : N.State) (i : N.Inputs) :
  R.v58344 (state s) (inputs i) = Zmod.unsigned (N.v58344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58344 s i)) at 1.
  unfold R.v58344, N.v58344.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58345 (s : N.State) (i : N.Inputs) :
  R.v58345 (state s) (inputs i) = Zmod.unsigned (N.v58345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58345 s i)) at 1.
  unfold R.v58345, N.v58345.
  unfold R.v6, N.v6.
  rewrite ?node_14456.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58346 (s : N.State) (i : N.Inputs) :
  R.v58346 (state s) (inputs i) = Zmod.unsigned (N.v58346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58346 s i)) at 1.
  unfold R.v58346, N.v58346.
  unfold R.v6, N.v6.
  rewrite ?node_14453.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58347 (s : N.State) (i : N.Inputs) :
  R.v58347 (state s) (inputs i) = Zmod.unsigned (N.v58347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58347 s i)) at 1.
  unfold R.v58347, N.v58347.
  rewrite ?node_58345.
  rewrite ?node_58346.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58348 (s : N.State) (i : N.Inputs) :
  R.v58348 (state s) (inputs i) = Zmod.unsigned (N.v58348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58348 s i)) at 1.
  unfold R.v58348, N.v58348.
  unfold R.v16463, N.v16463.
  rewrite ?node_58347.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58349 (s : N.State) (i : N.Inputs) :
  R.v58349 (state s) (inputs i) = Zmod.unsigned (N.v58349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58349 s i)) at 1.
  unfold R.v58349, N.v58349.
  rewrite ?node_14457.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58350 (s : N.State) (i : N.Inputs) :
  R.v58350 (state s) (inputs i) = Zmod.unsigned (N.v58350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58350 s i)) at 1.
  unfold R.v58350, N.v58350.
  unfold R.v6, N.v6.
  rewrite ?node_14550.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58351 (s : N.State) (i : N.Inputs) :
  R.v58351 (state s) (inputs i) = Zmod.unsigned (N.v58351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58351 s i)) at 1.
  unfold R.v58351, N.v58351.
  rewrite ?node_58349.
  rewrite ?node_58350.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58352 (s : N.State) (i : N.Inputs) :
  R.v58352 (state s) (inputs i) = Zmod.unsigned (N.v58352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58352 s i)) at 1.
  unfold R.v58352, N.v58352.
  rewrite ?node_58348.
  rewrite ?node_58351.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58353 (s : N.State) (i : N.Inputs) :
  R.v58353 (state s) (inputs i) = Zmod.unsigned (N.v58353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58353 s i)) at 1.
  unfold R.v58353, N.v58353.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58354 (s : N.State) (i : N.Inputs) :
  R.v58354 (state s) (inputs i) = Zmod.unsigned (N.v58354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58354 s i)) at 1.
  unfold R.v58354, N.v58354.
  unfold R.v6, N.v6.
  rewrite ?node_14547.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58355 (s : N.State) (i : N.Inputs) :
  R.v58355 (state s) (inputs i) = Zmod.unsigned (N.v58355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58355 s i)) at 1.
  unfold R.v58355, N.v58355.
  unfold R.v6, N.v6.
  rewrite ?node_14544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58356 (s : N.State) (i : N.Inputs) :
  R.v58356 (state s) (inputs i) = Zmod.unsigned (N.v58356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58356 s i)) at 1.
  unfold R.v58356, N.v58356.
  rewrite ?node_58354.
  rewrite ?node_58355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58357 (s : N.State) (i : N.Inputs) :
  R.v58357 (state s) (inputs i) = Zmod.unsigned (N.v58357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58357 s i)) at 1.
  unfold R.v58357, N.v58357.
  unfold R.v16463, N.v16463.
  rewrite ?node_58356.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58358 (s : N.State) (i : N.Inputs) :
  R.v58358 (state s) (inputs i) = Zmod.unsigned (N.v58358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58358 s i)) at 1.
  unfold R.v58358, N.v58358.
  rewrite ?node_14548.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58359 (s : N.State) (i : N.Inputs) :
  R.v58359 (state s) (inputs i) = Zmod.unsigned (N.v58359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58359 s i)) at 1.
  unfold R.v58359, N.v58359.
  unfold R.v6, N.v6.
  rewrite ?node_14640.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58360 (s : N.State) (i : N.Inputs) :
  R.v58360 (state s) (inputs i) = Zmod.unsigned (N.v58360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58360 s i)) at 1.
  unfold R.v58360, N.v58360.
  rewrite ?node_58358.
  rewrite ?node_58359.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58361 (s : N.State) (i : N.Inputs) :
  R.v58361 (state s) (inputs i) = Zmod.unsigned (N.v58361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58361 s i)) at 1.
  unfold R.v58361, N.v58361.
  rewrite ?node_58357.
  rewrite ?node_58360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58362 (s : N.State) (i : N.Inputs) :
  R.v58362 (state s) (inputs i) = Zmod.unsigned (N.v58362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58362 s i)) at 1.
  unfold R.v58362, N.v58362.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58363 (s : N.State) (i : N.Inputs) :
  R.v58363 (state s) (inputs i) = Zmod.unsigned (N.v58363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58363 s i)) at 1.
  unfold R.v58363, N.v58363.
  unfold R.v6, N.v6.
  rewrite ?node_14637.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58364 (s : N.State) (i : N.Inputs) :
  R.v58364 (state s) (inputs i) = Zmod.unsigned (N.v58364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58364 s i)) at 1.
  unfold R.v58364, N.v58364.
  unfold R.v6, N.v6.
  rewrite ?node_14634.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58365 (s : N.State) (i : N.Inputs) :
  R.v58365 (state s) (inputs i) = Zmod.unsigned (N.v58365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58365 s i)) at 1.
  unfold R.v58365, N.v58365.
  rewrite ?node_58363.
  rewrite ?node_58364.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58366 (s : N.State) (i : N.Inputs) :
  R.v58366 (state s) (inputs i) = Zmod.unsigned (N.v58366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58366 s i)) at 1.
  unfold R.v58366, N.v58366.
  unfold R.v16463, N.v16463.
  rewrite ?node_58365.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58367 (s : N.State) (i : N.Inputs) :
  R.v58367 (state s) (inputs i) = Zmod.unsigned (N.v58367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58367 s i)) at 1.
  unfold R.v58367, N.v58367.
  rewrite ?node_14638.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58368 (s : N.State) (i : N.Inputs) :
  R.v58368 (state s) (inputs i) = Zmod.unsigned (N.v58368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58368 s i)) at 1.
  unfold R.v58368, N.v58368.
  unfold R.v6, N.v6.
  rewrite ?node_14728.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58369 (s : N.State) (i : N.Inputs) :
  R.v58369 (state s) (inputs i) = Zmod.unsigned (N.v58369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58369 s i)) at 1.
  unfold R.v58369, N.v58369.
  rewrite ?node_58367.
  rewrite ?node_58368.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58370 (s : N.State) (i : N.Inputs) :
  R.v58370 (state s) (inputs i) = Zmod.unsigned (N.v58370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58370 s i)) at 1.
  unfold R.v58370, N.v58370.
  rewrite ?node_58366.
  rewrite ?node_58369.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58371 (s : N.State) (i : N.Inputs) :
  R.v58371 (state s) (inputs i) = Zmod.unsigned (N.v58371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58371 s i)) at 1.
  unfold R.v58371, N.v58371.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58372 (s : N.State) (i : N.Inputs) :
  R.v58372 (state s) (inputs i) = Zmod.unsigned (N.v58372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58372 s i)) at 1.
  unfold R.v58372, N.v58372.
  unfold R.v6, N.v6.
  rewrite ?node_14725.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58373 (s : N.State) (i : N.Inputs) :
  R.v58373 (state s) (inputs i) = Zmod.unsigned (N.v58373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58373 s i)) at 1.
  unfold R.v58373, N.v58373.
  unfold R.v6, N.v6.
  rewrite ?node_14722.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58374 (s : N.State) (i : N.Inputs) :
  R.v58374 (state s) (inputs i) = Zmod.unsigned (N.v58374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58374 s i)) at 1.
  unfold R.v58374, N.v58374.
  rewrite ?node_58372.
  rewrite ?node_58373.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58375 (s : N.State) (i : N.Inputs) :
  R.v58375 (state s) (inputs i) = Zmod.unsigned (N.v58375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58375 s i)) at 1.
  unfold R.v58375, N.v58375.
  unfold R.v16463, N.v16463.
  rewrite ?node_58374.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58376 (s : N.State) (i : N.Inputs) :
  R.v58376 (state s) (inputs i) = Zmod.unsigned (N.v58376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58376 s i)) at 1.
  unfold R.v58376, N.v58376.
  rewrite ?node_14726.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58377 (s : N.State) (i : N.Inputs) :
  R.v58377 (state s) (inputs i) = Zmod.unsigned (N.v58377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58377 s i)) at 1.
  unfold R.v58377, N.v58377.
  unfold R.v6, N.v6.
  rewrite ?node_14815.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58378 (s : N.State) (i : N.Inputs) :
  R.v58378 (state s) (inputs i) = Zmod.unsigned (N.v58378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58378 s i)) at 1.
  unfold R.v58378, N.v58378.
  rewrite ?node_58376.
  rewrite ?node_58377.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58379 (s : N.State) (i : N.Inputs) :
  R.v58379 (state s) (inputs i) = Zmod.unsigned (N.v58379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58379 s i)) at 1.
  unfold R.v58379, N.v58379.
  rewrite ?node_58375.
  rewrite ?node_58378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58380 (s : N.State) (i : N.Inputs) :
  R.v58380 (state s) (inputs i) = Zmod.unsigned (N.v58380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58380 s i)) at 1.
  unfold R.v58380, N.v58380.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58381 (s : N.State) (i : N.Inputs) :
  R.v58381 (state s) (inputs i) = Zmod.unsigned (N.v58381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58381 s i)) at 1.
  unfold R.v58381, N.v58381.
  unfold R.v6, N.v6.
  rewrite ?node_14812.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58382 (s : N.State) (i : N.Inputs) :
  R.v58382 (state s) (inputs i) = Zmod.unsigned (N.v58382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58382 s i)) at 1.
  unfold R.v58382, N.v58382.
  unfold R.v6, N.v6.
  rewrite ?node_14809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58383 (s : N.State) (i : N.Inputs) :
  R.v58383 (state s) (inputs i) = Zmod.unsigned (N.v58383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58383 s i)) at 1.
  unfold R.v58383, N.v58383.
  rewrite ?node_58381.
  rewrite ?node_58382.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58384 (s : N.State) (i : N.Inputs) :
  R.v58384 (state s) (inputs i) = Zmod.unsigned (N.v58384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58384 s i)) at 1.
  unfold R.v58384, N.v58384.
  unfold R.v16463, N.v16463.
  rewrite ?node_58383.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58385 (s : N.State) (i : N.Inputs) :
  R.v58385 (state s) (inputs i) = Zmod.unsigned (N.v58385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58385 s i)) at 1.
  unfold R.v58385, N.v58385.
  rewrite ?node_14813.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58386 (s : N.State) (i : N.Inputs) :
  R.v58386 (state s) (inputs i) = Zmod.unsigned (N.v58386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58386 s i)) at 1.
  unfold R.v58386, N.v58386.
  unfold R.v6, N.v6.
  rewrite ?node_14898.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58387 (s : N.State) (i : N.Inputs) :
  R.v58387 (state s) (inputs i) = Zmod.unsigned (N.v58387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58387 s i)) at 1.
  unfold R.v58387, N.v58387.
  rewrite ?node_58385.
  rewrite ?node_58386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58388 (s : N.State) (i : N.Inputs) :
  R.v58388 (state s) (inputs i) = Zmod.unsigned (N.v58388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58388 s i)) at 1.
  unfold R.v58388, N.v58388.
  rewrite ?node_58384.
  rewrite ?node_58387.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58389 (s : N.State) (i : N.Inputs) :
  R.v58389 (state s) (inputs i) = Zmod.unsigned (N.v58389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58389 s i)) at 1.
  unfold R.v58389, N.v58389.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58390 (s : N.State) (i : N.Inputs) :
  R.v58390 (state s) (inputs i) = Zmod.unsigned (N.v58390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58390 s i)) at 1.
  unfold R.v58390, N.v58390.
  rewrite ?node_14895.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58391 (s : N.State) (i : N.Inputs) :
  R.v58391 (state s) (inputs i) = Zmod.unsigned (N.v58391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58391 s i)) at 1.
  unfold R.v58391, N.v58391.
  unfold R.v6, N.v6.
  rewrite ?node_14891.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58392 (s : N.State) (i : N.Inputs) :
  R.v58392 (state s) (inputs i) = Zmod.unsigned (N.v58392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58392 s i)) at 1.
  unfold R.v58392, N.v58392.
  unfold R.v6, N.v6.
  rewrite ?node_14888.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58393 (s : N.State) (i : N.Inputs) :
  R.v58393 (state s) (inputs i) = Zmod.unsigned (N.v58393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58393 s i)) at 1.
  unfold R.v58393, N.v58393.
  rewrite ?node_58391.
  rewrite ?node_58392.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58394 (s : N.State) (i : N.Inputs) :
  R.v58394 (state s) (inputs i) = Zmod.unsigned (N.v58394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58394 s i)) at 1.
  unfold R.v58394, N.v58394.
  unfold R.v16484, N.v16484.
  rewrite ?node_58393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58395 (s : N.State) (i : N.Inputs) :
  R.v58395 (state s) (inputs i) = Zmod.unsigned (N.v58395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58395 s i)) at 1.
  unfold R.v58395, N.v58395.
  rewrite ?node_58390.
  rewrite ?node_58394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58396 (s : N.State) (i : N.Inputs) :
  R.v58396 (state s) (inputs i) = Zmod.unsigned (N.v58396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58396 s i)) at 1.
  unfold R.v58396, N.v58396.
  unfold R.v6, N.v6.
  rewrite ?node_58395.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58397 (s : N.State) (i : N.Inputs) :
  R.v58397 (state s) (inputs i) = Zmod.unsigned (N.v58397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58397 s i)) at 1.
  unfold R.v58397, N.v58397.
  rewrite ?node_14896.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58398 (s : N.State) (i : N.Inputs) :
  R.v58398 (state s) (inputs i) = Zmod.unsigned (N.v58398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58398 s i)) at 1.
  unfold R.v58398, N.v58398.
  unfold R.v6, N.v6.
  rewrite ?node_14978.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58399 (s : N.State) (i : N.Inputs) :
  R.v58399 (state s) (inputs i) = Zmod.unsigned (N.v58399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58399 s i)) at 1.
  unfold R.v58399, N.v58399.
  rewrite ?node_58397.
  rewrite ?node_58398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58400 (s : N.State) (i : N.Inputs) :
  R.v58400 (state s) (inputs i) = Zmod.unsigned (N.v58400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58400 s i)) at 1.
  unfold R.v58400, N.v58400.
  rewrite ?node_58396.
  rewrite ?node_58399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58401 (s : N.State) (i : N.Inputs) :
  R.v58401 (state s) (inputs i) = Zmod.unsigned (N.v58401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58401 s i)) at 1.
  unfold R.v58401, N.v58401.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58402 (s : N.State) (i : N.Inputs) :
  R.v58402 (state s) (inputs i) = Zmod.unsigned (N.v58402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58402 s i)) at 1.
  unfold R.v58402, N.v58402.
  unfold R.v6, N.v6.
  rewrite ?node_14973.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58403 (s : N.State) (i : N.Inputs) :
  R.v58403 (state s) (inputs i) = Zmod.unsigned (N.v58403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58403 s i)) at 1.
  unfold R.v58403, N.v58403.
  unfold R.v6, N.v6.
  rewrite ?node_14970.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58404 (s : N.State) (i : N.Inputs) :
  R.v58404 (state s) (inputs i) = Zmod.unsigned (N.v58404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58404 s i)) at 1.
  unfold R.v58404, N.v58404.
  rewrite ?node_58402.
  rewrite ?node_58403.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58405 (s : N.State) (i : N.Inputs) :
  R.v58405 (state s) (inputs i) = Zmod.unsigned (N.v58405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58405 s i)) at 1.
  unfold R.v58405, N.v58405.
  unfold R.v16463, N.v16463.
  rewrite ?node_58404.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58406 (s : N.State) (i : N.Inputs) :
  R.v58406 (state s) (inputs i) = Zmod.unsigned (N.v58406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58406 s i)) at 1.
  unfold R.v58406, N.v58406.
  rewrite ?node_14974.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58407 (s : N.State) (i : N.Inputs) :
  R.v58407 (state s) (inputs i) = Zmod.unsigned (N.v58407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58407 s i)) at 1.
  unfold R.v58407, N.v58407.
  unfold R.v6, N.v6.
  rewrite ?node_15052.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58408 (s : N.State) (i : N.Inputs) :
  R.v58408 (state s) (inputs i) = Zmod.unsigned (N.v58408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58408 s i)) at 1.
  unfold R.v58408, N.v58408.
  rewrite ?node_58406.
  rewrite ?node_58407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58409 (s : N.State) (i : N.Inputs) :
  R.v58409 (state s) (inputs i) = Zmod.unsigned (N.v58409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58409 s i)) at 1.
  unfold R.v58409, N.v58409.
  rewrite ?node_58405.
  rewrite ?node_58408.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58410 (s : N.State) (i : N.Inputs) :
  R.v58410 (state s) (inputs i) = Zmod.unsigned (N.v58410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58410 s i)) at 1.
  unfold R.v58410, N.v58410.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58411 (s : N.State) (i : N.Inputs) :
  R.v58411 (state s) (inputs i) = Zmod.unsigned (N.v58411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58411 s i)) at 1.
  unfold R.v58411, N.v58411.
  unfold R.v6, N.v6.
  rewrite ?node_15049.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58412 (s : N.State) (i : N.Inputs) :
  R.v58412 (state s) (inputs i) = Zmod.unsigned (N.v58412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58412 s i)) at 1.
  unfold R.v58412, N.v58412.
  unfold R.v6, N.v6.
  rewrite ?node_15048.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58413 (s : N.State) (i : N.Inputs) :
  R.v58413 (state s) (inputs i) = Zmod.unsigned (N.v58413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58413 s i)) at 1.
  unfold R.v58413, N.v58413.
  rewrite ?node_58411.
  rewrite ?node_58412.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58414 (s : N.State) (i : N.Inputs) :
  R.v58414 (state s) (inputs i) = Zmod.unsigned (N.v58414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58414 s i)) at 1.
  unfold R.v58414, N.v58414.
  unfold R.v16463, N.v16463.
  rewrite ?node_58413.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58415 (s : N.State) (i : N.Inputs) :
  R.v58415 (state s) (inputs i) = Zmod.unsigned (N.v58415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58415 s i)) at 1.
  unfold R.v58415, N.v58415.
  rewrite ?node_15050.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58416 (s : N.State) (i : N.Inputs) :
  R.v58416 (state s) (inputs i) = Zmod.unsigned (N.v58416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58416 s i)) at 1.
  unfold R.v58416, N.v58416.
  unfold R.v6, N.v6.
  rewrite ?node_15125.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58417 (s : N.State) (i : N.Inputs) :
  R.v58417 (state s) (inputs i) = Zmod.unsigned (N.v58417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58417 s i)) at 1.
  unfold R.v58417, N.v58417.
  rewrite ?node_58415.
  rewrite ?node_58416.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58418 (s : N.State) (i : N.Inputs) :
  R.v58418 (state s) (inputs i) = Zmod.unsigned (N.v58418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58418 s i)) at 1.
  unfold R.v58418, N.v58418.
  rewrite ?node_58414.
  rewrite ?node_58417.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58419 (s : N.State) (i : N.Inputs) :
  R.v58419 (state s) (inputs i) = Zmod.unsigned (N.v58419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58419 s i)) at 1.
  unfold R.v58419, N.v58419.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58420 (s : N.State) (i : N.Inputs) :
  R.v58420 (state s) (inputs i) = Zmod.unsigned (N.v58420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58420 s i)) at 1.
  unfold R.v58420, N.v58420.
  unfold R.v6, N.v6.
  rewrite ?node_15122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58421 (s : N.State) (i : N.Inputs) :
  R.v58421 (state s) (inputs i) = Zmod.unsigned (N.v58421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58421 s i)) at 1.
  unfold R.v58421, N.v58421.
  unfold R.v6, N.v6.
  rewrite ?node_15119.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58422 (s : N.State) (i : N.Inputs) :
  R.v58422 (state s) (inputs i) = Zmod.unsigned (N.v58422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58422 s i)) at 1.
  unfold R.v58422, N.v58422.
  rewrite ?node_58420.
  rewrite ?node_58421.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58423 (s : N.State) (i : N.Inputs) :
  R.v58423 (state s) (inputs i) = Zmod.unsigned (N.v58423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58423 s i)) at 1.
  unfold R.v58423, N.v58423.
  unfold R.v16463, N.v16463.
  rewrite ?node_58422.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58424 (s : N.State) (i : N.Inputs) :
  R.v58424 (state s) (inputs i) = Zmod.unsigned (N.v58424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58424 s i)) at 1.
  unfold R.v58424, N.v58424.
  rewrite ?node_15123.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58425 (s : N.State) (i : N.Inputs) :
  R.v58425 (state s) (inputs i) = Zmod.unsigned (N.v58425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58425 s i)) at 1.
  unfold R.v58425, N.v58425.
  unfold R.v6, N.v6.
  rewrite ?node_15194.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58426 (s : N.State) (i : N.Inputs) :
  R.v58426 (state s) (inputs i) = Zmod.unsigned (N.v58426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58426 s i)) at 1.
  unfold R.v58426, N.v58426.
  rewrite ?node_58424.
  rewrite ?node_58425.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58427 (s : N.State) (i : N.Inputs) :
  R.v58427 (state s) (inputs i) = Zmod.unsigned (N.v58427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58427 s i)) at 1.
  unfold R.v58427, N.v58427.
  rewrite ?node_58423.
  rewrite ?node_58426.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58428 (s : N.State) (i : N.Inputs) :
  R.v58428 (state s) (inputs i) = Zmod.unsigned (N.v58428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58428 s i)) at 1.
  unfold R.v58428, N.v58428.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58429 (s : N.State) (i : N.Inputs) :
  R.v58429 (state s) (inputs i) = Zmod.unsigned (N.v58429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58429 s i)) at 1.
  unfold R.v58429, N.v58429.
  unfold R.v6, N.v6.
  rewrite ?node_15191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58430 (s : N.State) (i : N.Inputs) :
  R.v58430 (state s) (inputs i) = Zmod.unsigned (N.v58430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58430 s i)) at 1.
  unfold R.v58430, N.v58430.
  unfold R.v6, N.v6.
  rewrite ?node_15190.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58431 (s : N.State) (i : N.Inputs) :
  R.v58431 (state s) (inputs i) = Zmod.unsigned (N.v58431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58431 s i)) at 1.
  unfold R.v58431, N.v58431.
  rewrite ?node_58429.
  rewrite ?node_58430.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58432 (s : N.State) (i : N.Inputs) :
  R.v58432 (state s) (inputs i) = Zmod.unsigned (N.v58432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58432 s i)) at 1.
  unfold R.v58432, N.v58432.
  unfold R.v16463, N.v16463.
  rewrite ?node_58431.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58433 (s : N.State) (i : N.Inputs) :
  R.v58433 (state s) (inputs i) = Zmod.unsigned (N.v58433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58433 s i)) at 1.
  unfold R.v58433, N.v58433.
  rewrite ?node_15192.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58434 (s : N.State) (i : N.Inputs) :
  R.v58434 (state s) (inputs i) = Zmod.unsigned (N.v58434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58434 s i)) at 1.
  unfold R.v58434, N.v58434.
  unfold R.v6, N.v6.
  rewrite ?node_15262.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58435 (s : N.State) (i : N.Inputs) :
  R.v58435 (state s) (inputs i) = Zmod.unsigned (N.v58435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58435 s i)) at 1.
  unfold R.v58435, N.v58435.
  rewrite ?node_58433.
  rewrite ?node_58434.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58436 (s : N.State) (i : N.Inputs) :
  R.v58436 (state s) (inputs i) = Zmod.unsigned (N.v58436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58436 s i)) at 1.
  unfold R.v58436, N.v58436.
  rewrite ?node_58432.
  rewrite ?node_58435.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58437 (s : N.State) (i : N.Inputs) :
  R.v58437 (state s) (inputs i) = Zmod.unsigned (N.v58437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58437 s i)) at 1.
  unfold R.v58437, N.v58437.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58438 (s : N.State) (i : N.Inputs) :
  R.v58438 (state s) (inputs i) = Zmod.unsigned (N.v58438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58438 s i)) at 1.
  unfold R.v58438, N.v58438.
  unfold R.v6, N.v6.
  rewrite ?node_15259.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58439 (s : N.State) (i : N.Inputs) :
  R.v58439 (state s) (inputs i) = Zmod.unsigned (N.v58439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58439 s i)) at 1.
  unfold R.v58439, N.v58439.
  unfold R.v6, N.v6.
  rewrite ?node_15258.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58440 (s : N.State) (i : N.Inputs) :
  R.v58440 (state s) (inputs i) = Zmod.unsigned (N.v58440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58440 s i)) at 1.
  unfold R.v58440, N.v58440.
  rewrite ?node_58438.
  rewrite ?node_58439.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58441 (s : N.State) (i : N.Inputs) :
  R.v58441 (state s) (inputs i) = Zmod.unsigned (N.v58441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58441 s i)) at 1.
  unfold R.v58441, N.v58441.
  unfold R.v16463, N.v16463.
  rewrite ?node_58440.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58442 (s : N.State) (i : N.Inputs) :
  R.v58442 (state s) (inputs i) = Zmod.unsigned (N.v58442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58442 s i)) at 1.
  unfold R.v58442, N.v58442.
  rewrite ?node_15260.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58443 (s : N.State) (i : N.Inputs) :
  R.v58443 (state s) (inputs i) = Zmod.unsigned (N.v58443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58443 s i)) at 1.
  unfold R.v58443, N.v58443.
  unfold R.v6, N.v6.
  rewrite ?node_15328.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58444 (s : N.State) (i : N.Inputs) :
  R.v58444 (state s) (inputs i) = Zmod.unsigned (N.v58444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58444 s i)) at 1.
  unfold R.v58444, N.v58444.
  rewrite ?node_58442.
  rewrite ?node_58443.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58445 (s : N.State) (i : N.Inputs) :
  R.v58445 (state s) (inputs i) = Zmod.unsigned (N.v58445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58445 s i)) at 1.
  unfold R.v58445, N.v58445.
  rewrite ?node_58441.
  rewrite ?node_58444.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58446 (s : N.State) (i : N.Inputs) :
  R.v58446 (state s) (inputs i) = Zmod.unsigned (N.v58446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58446 s i)) at 1.
  unfold R.v58446, N.v58446.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58447 (s : N.State) (i : N.Inputs) :
  R.v58447 (state s) (inputs i) = Zmod.unsigned (N.v58447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58447 s i)) at 1.
  unfold R.v58447, N.v58447.
  unfold R.v6, N.v6.
  rewrite ?node_15325.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58448 (s : N.State) (i : N.Inputs) :
  R.v58448 (state s) (inputs i) = Zmod.unsigned (N.v58448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58448 s i)) at 1.
  unfold R.v58448, N.v58448.
  unfold R.v6, N.v6.
  rewrite ?node_15324.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58449 (s : N.State) (i : N.Inputs) :
  R.v58449 (state s) (inputs i) = Zmod.unsigned (N.v58449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58449 s i)) at 1.
  unfold R.v58449, N.v58449.
  rewrite ?node_58447.
  rewrite ?node_58448.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58450 (s : N.State) (i : N.Inputs) :
  R.v58450 (state s) (inputs i) = Zmod.unsigned (N.v58450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58450 s i)) at 1.
  unfold R.v58450, N.v58450.
  unfold R.v16463, N.v16463.
  rewrite ?node_58449.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58451 (s : N.State) (i : N.Inputs) :
  R.v58451 (state s) (inputs i) = Zmod.unsigned (N.v58451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58451 s i)) at 1.
  unfold R.v58451, N.v58451.
  rewrite ?node_15326.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58452 (s : N.State) (i : N.Inputs) :
  R.v58452 (state s) (inputs i) = Zmod.unsigned (N.v58452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58452 s i)) at 1.
  unfold R.v58452, N.v58452.
  unfold R.v6, N.v6.
  rewrite ?node_15393.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58453 (s : N.State) (i : N.Inputs) :
  R.v58453 (state s) (inputs i) = Zmod.unsigned (N.v58453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58453 s i)) at 1.
  unfold R.v58453, N.v58453.
  rewrite ?node_58451.
  rewrite ?node_58452.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58454 (s : N.State) (i : N.Inputs) :
  R.v58454 (state s) (inputs i) = Zmod.unsigned (N.v58454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58454 s i)) at 1.
  unfold R.v58454, N.v58454.
  rewrite ?node_58450.
  rewrite ?node_58453.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58455 (s : N.State) (i : N.Inputs) :
  R.v58455 (state s) (inputs i) = Zmod.unsigned (N.v58455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58455 s i)) at 1.
  unfold R.v58455, N.v58455.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58456 (s : N.State) (i : N.Inputs) :
  R.v58456 (state s) (inputs i) = Zmod.unsigned (N.v58456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58456 s i)) at 1.
  unfold R.v58456, N.v58456.
  unfold R.v6, N.v6.
  rewrite ?node_15390.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58457 (s : N.State) (i : N.Inputs) :
  R.v58457 (state s) (inputs i) = Zmod.unsigned (N.v58457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58457 s i)) at 1.
  unfold R.v58457, N.v58457.
  unfold R.v6, N.v6.
  rewrite ?node_15389.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58458 (s : N.State) (i : N.Inputs) :
  R.v58458 (state s) (inputs i) = Zmod.unsigned (N.v58458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58458 s i)) at 1.
  unfold R.v58458, N.v58458.
  rewrite ?node_58456.
  rewrite ?node_58457.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58459 (s : N.State) (i : N.Inputs) :
  R.v58459 (state s) (inputs i) = Zmod.unsigned (N.v58459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58459 s i)) at 1.
  unfold R.v58459, N.v58459.
  unfold R.v16463, N.v16463.
  rewrite ?node_58458.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58460 (s : N.State) (i : N.Inputs) :
  R.v58460 (state s) (inputs i) = Zmod.unsigned (N.v58460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58460 s i)) at 1.
  unfold R.v58460, N.v58460.
  rewrite ?node_15391.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58461 (s : N.State) (i : N.Inputs) :
  R.v58461 (state s) (inputs i) = Zmod.unsigned (N.v58461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58461 s i)) at 1.
  unfold R.v58461, N.v58461.
  unfold R.v6, N.v6.
  rewrite ?node_15454.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58462 (s : N.State) (i : N.Inputs) :
  R.v58462 (state s) (inputs i) = Zmod.unsigned (N.v58462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58462 s i)) at 1.
  unfold R.v58462, N.v58462.
  rewrite ?node_58460.
  rewrite ?node_58461.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58463 (s : N.State) (i : N.Inputs) :
  R.v58463 (state s) (inputs i) = Zmod.unsigned (N.v58463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58463 s i)) at 1.
  unfold R.v58463, N.v58463.
  rewrite ?node_58459.
  rewrite ?node_58462.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58464 (s : N.State) (i : N.Inputs) :
  R.v58464 (state s) (inputs i) = Zmod.unsigned (N.v58464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58464 s i)) at 1.
  unfold R.v58464, N.v58464.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58465 (s : N.State) (i : N.Inputs) :
  R.v58465 (state s) (inputs i) = Zmod.unsigned (N.v58465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58465 s i)) at 1.
  unfold R.v58465, N.v58465.
  unfold R.v6, N.v6.
  rewrite ?node_15451.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58466 (s : N.State) (i : N.Inputs) :
  R.v58466 (state s) (inputs i) = Zmod.unsigned (N.v58466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58466 s i)) at 1.
  unfold R.v58466, N.v58466.
  unfold R.v6, N.v6.
  rewrite ?node_15448.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58467 (s : N.State) (i : N.Inputs) :
  R.v58467 (state s) (inputs i) = Zmod.unsigned (N.v58467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58467 s i)) at 1.
  unfold R.v58467, N.v58467.
  rewrite ?node_58465.
  rewrite ?node_58466.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58468 (s : N.State) (i : N.Inputs) :
  R.v58468 (state s) (inputs i) = Zmod.unsigned (N.v58468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58468 s i)) at 1.
  unfold R.v58468, N.v58468.
  unfold R.v16463, N.v16463.
  rewrite ?node_58467.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58469 (s : N.State) (i : N.Inputs) :
  R.v58469 (state s) (inputs i) = Zmod.unsigned (N.v58469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58469 s i)) at 1.
  unfold R.v58469, N.v58469.
  rewrite ?node_15452.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58470 (s : N.State) (i : N.Inputs) :
  R.v58470 (state s) (inputs i) = Zmod.unsigned (N.v58470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58470 s i)) at 1.
  unfold R.v58470, N.v58470.
  unfold R.v6, N.v6.
  rewrite ?node_15512.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58471 (s : N.State) (i : N.Inputs) :
  R.v58471 (state s) (inputs i) = Zmod.unsigned (N.v58471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58471 s i)) at 1.
  unfold R.v58471, N.v58471.
  rewrite ?node_58469.
  rewrite ?node_58470.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58472 (s : N.State) (i : N.Inputs) :
  R.v58472 (state s) (inputs i) = Zmod.unsigned (N.v58472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58472 s i)) at 1.
  unfold R.v58472, N.v58472.
  rewrite ?node_58468.
  rewrite ?node_58471.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58473 (s : N.State) (i : N.Inputs) :
  R.v58473 (state s) (inputs i) = Zmod.unsigned (N.v58473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58473 s i)) at 1.
  unfold R.v58473, N.v58473.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58474 (s : N.State) (i : N.Inputs) :
  R.v58474 (state s) (inputs i) = Zmod.unsigned (N.v58474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58474 s i)) at 1.
  unfold R.v58474, N.v58474.
  unfold R.v6, N.v6.
  rewrite ?node_15509.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58475 (s : N.State) (i : N.Inputs) :
  R.v58475 (state s) (inputs i) = Zmod.unsigned (N.v58475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58475 s i)) at 1.
  unfold R.v58475, N.v58475.
  unfold R.v6, N.v6.
  rewrite ?node_15508.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58476 (s : N.State) (i : N.Inputs) :
  R.v58476 (state s) (inputs i) = Zmod.unsigned (N.v58476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58476 s i)) at 1.
  unfold R.v58476, N.v58476.
  rewrite ?node_58474.
  rewrite ?node_58475.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58477 (s : N.State) (i : N.Inputs) :
  R.v58477 (state s) (inputs i) = Zmod.unsigned (N.v58477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58477 s i)) at 1.
  unfold R.v58477, N.v58477.
  unfold R.v16463, N.v16463.
  rewrite ?node_58476.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58478 (s : N.State) (i : N.Inputs) :
  R.v58478 (state s) (inputs i) = Zmod.unsigned (N.v58478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58478 s i)) at 1.
  unfold R.v58478, N.v58478.
  rewrite ?node_15510.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58479 (s : N.State) (i : N.Inputs) :
  R.v58479 (state s) (inputs i) = Zmod.unsigned (N.v58479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58479 s i)) at 1.
  unfold R.v58479, N.v58479.
  unfold R.v6, N.v6.
  rewrite ?node_15568.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58480 (s : N.State) (i : N.Inputs) :
  R.v58480 (state s) (inputs i) = Zmod.unsigned (N.v58480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58480 s i)) at 1.
  unfold R.v58480, N.v58480.
  rewrite ?node_58478.
  rewrite ?node_58479.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58481 (s : N.State) (i : N.Inputs) :
  R.v58481 (state s) (inputs i) = Zmod.unsigned (N.v58481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58481 s i)) at 1.
  unfold R.v58481, N.v58481.
  rewrite ?node_58477.
  rewrite ?node_58480.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58482 (s : N.State) (i : N.Inputs) :
  R.v58482 (state s) (inputs i) = Zmod.unsigned (N.v58482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58482 s i)) at 1.
  unfold R.v58482, N.v58482.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58483 (s : N.State) (i : N.Inputs) :
  R.v58483 (state s) (inputs i) = Zmod.unsigned (N.v58483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58483 s i)) at 1.
  unfold R.v58483, N.v58483.
  unfold R.v6, N.v6.
  rewrite ?node_15565.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58484 (s : N.State) (i : N.Inputs) :
  R.v58484 (state s) (inputs i) = Zmod.unsigned (N.v58484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58484 s i)) at 1.
  unfold R.v58484, N.v58484.
  unfold R.v6, N.v6.
  rewrite ?node_15564.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58485 (s : N.State) (i : N.Inputs) :
  R.v58485 (state s) (inputs i) = Zmod.unsigned (N.v58485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58485 s i)) at 1.
  unfold R.v58485, N.v58485.
  rewrite ?node_58483.
  rewrite ?node_58484.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58486 (s : N.State) (i : N.Inputs) :
  R.v58486 (state s) (inputs i) = Zmod.unsigned (N.v58486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58486 s i)) at 1.
  unfold R.v58486, N.v58486.
  unfold R.v16463, N.v16463.
  rewrite ?node_58485.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58487 (s : N.State) (i : N.Inputs) :
  R.v58487 (state s) (inputs i) = Zmod.unsigned (N.v58487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58487 s i)) at 1.
  unfold R.v58487, N.v58487.
  rewrite ?node_15566.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58488 (s : N.State) (i : N.Inputs) :
  R.v58488 (state s) (inputs i) = Zmod.unsigned (N.v58488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58488 s i)) at 1.
  unfold R.v58488, N.v58488.
  unfold R.v6, N.v6.
  rewrite ?node_15623.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58489 (s : N.State) (i : N.Inputs) :
  R.v58489 (state s) (inputs i) = Zmod.unsigned (N.v58489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58489 s i)) at 1.
  unfold R.v58489, N.v58489.
  rewrite ?node_58487.
  rewrite ?node_58488.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58490 (s : N.State) (i : N.Inputs) :
  R.v58490 (state s) (inputs i) = Zmod.unsigned (N.v58490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58490 s i)) at 1.
  unfold R.v58490, N.v58490.
  rewrite ?node_58486.
  rewrite ?node_58489.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58491 (s : N.State) (i : N.Inputs) :
  R.v58491 (state s) (inputs i) = Zmod.unsigned (N.v58491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58491 s i)) at 1.
  unfold R.v58491, N.v58491.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58492 (s : N.State) (i : N.Inputs) :
  R.v58492 (state s) (inputs i) = Zmod.unsigned (N.v58492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58492 s i)) at 1.
  unfold R.v58492, N.v58492.
  unfold R.v6, N.v6.
  rewrite ?node_15620.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58493 (s : N.State) (i : N.Inputs) :
  R.v58493 (state s) (inputs i) = Zmod.unsigned (N.v58493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58493 s i)) at 1.
  unfold R.v58493, N.v58493.
  unfold R.v6, N.v6.
  rewrite ?node_15619.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58494 (s : N.State) (i : N.Inputs) :
  R.v58494 (state s) (inputs i) = Zmod.unsigned (N.v58494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58494 s i)) at 1.
  unfold R.v58494, N.v58494.
  rewrite ?node_58492.
  rewrite ?node_58493.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58495 (s : N.State) (i : N.Inputs) :
  R.v58495 (state s) (inputs i) = Zmod.unsigned (N.v58495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58495 s i)) at 1.
  unfold R.v58495, N.v58495.
  unfold R.v16463, N.v16463.
  rewrite ?node_58494.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58496 (s : N.State) (i : N.Inputs) :
  R.v58496 (state s) (inputs i) = Zmod.unsigned (N.v58496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58496 s i)) at 1.
  unfold R.v58496, N.v58496.
  rewrite ?node_15621.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58497 (s : N.State) (i : N.Inputs) :
  R.v58497 (state s) (inputs i) = Zmod.unsigned (N.v58497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58497 s i)) at 1.
  unfold R.v58497, N.v58497.
  unfold R.v6, N.v6.
  rewrite ?node_15674.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58498 (s : N.State) (i : N.Inputs) :
  R.v58498 (state s) (inputs i) = Zmod.unsigned (N.v58498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58498 s i)) at 1.
  unfold R.v58498, N.v58498.
  rewrite ?node_58496.
  rewrite ?node_58497.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58499 (s : N.State) (i : N.Inputs) :
  R.v58499 (state s) (inputs i) = Zmod.unsigned (N.v58499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58499 s i)) at 1.
  unfold R.v58499, N.v58499.
  rewrite ?node_58495.
  rewrite ?node_58498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58500 (s : N.State) (i : N.Inputs) :
  R.v58500 (state s) (inputs i) = Zmod.unsigned (N.v58500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58500 s i)) at 1.
  unfold R.v58500, N.v58500.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58501 (s : N.State) (i : N.Inputs) :
  R.v58501 (state s) (inputs i) = Zmod.unsigned (N.v58501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58501 s i)) at 1.
  unfold R.v58501, N.v58501.
  unfold R.v6, N.v6.
  rewrite ?node_15671.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58502 (s : N.State) (i : N.Inputs) :
  R.v58502 (state s) (inputs i) = Zmod.unsigned (N.v58502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58502 s i)) at 1.
  unfold R.v58502, N.v58502.
  unfold R.v6, N.v6.
  rewrite ?node_15670.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58503 (s : N.State) (i : N.Inputs) :
  R.v58503 (state s) (inputs i) = Zmod.unsigned (N.v58503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58503 s i)) at 1.
  unfold R.v58503, N.v58503.
  rewrite ?node_58501.
  rewrite ?node_58502.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58504 (s : N.State) (i : N.Inputs) :
  R.v58504 (state s) (inputs i) = Zmod.unsigned (N.v58504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58504 s i)) at 1.
  unfold R.v58504, N.v58504.
  unfold R.v16463, N.v16463.
  rewrite ?node_58503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58505 (s : N.State) (i : N.Inputs) :
  R.v58505 (state s) (inputs i) = Zmod.unsigned (N.v58505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58505 s i)) at 1.
  unfold R.v58505, N.v58505.
  rewrite ?node_15672.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58506 (s : N.State) (i : N.Inputs) :
  R.v58506 (state s) (inputs i) = Zmod.unsigned (N.v58506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58506 s i)) at 1.
  unfold R.v58506, N.v58506.
  unfold R.v6, N.v6.
  rewrite ?node_15724.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58507 (s : N.State) (i : N.Inputs) :
  R.v58507 (state s) (inputs i) = Zmod.unsigned (N.v58507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58507 s i)) at 1.
  unfold R.v58507, N.v58507.
  rewrite ?node_58505.
  rewrite ?node_58506.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58508 (s : N.State) (i : N.Inputs) :
  R.v58508 (state s) (inputs i) = Zmod.unsigned (N.v58508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58508 s i)) at 1.
  unfold R.v58508, N.v58508.
  rewrite ?node_58504.
  rewrite ?node_58507.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58509 (s : N.State) (i : N.Inputs) :
  R.v58509 (state s) (inputs i) = Zmod.unsigned (N.v58509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58509 s i)) at 1.
  unfold R.v58509, N.v58509.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58510 (s : N.State) (i : N.Inputs) :
  R.v58510 (state s) (inputs i) = Zmod.unsigned (N.v58510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58510 s i)) at 1.
  unfold R.v58510, N.v58510.
  unfold R.v6, N.v6.
  rewrite ?node_15721.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58511 (s : N.State) (i : N.Inputs) :
  R.v58511 (state s) (inputs i) = Zmod.unsigned (N.v58511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58511 s i)) at 1.
  unfold R.v58511, N.v58511.
  unfold R.v6, N.v6.
  rewrite ?node_15720.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58512 (s : N.State) (i : N.Inputs) :
  R.v58512 (state s) (inputs i) = Zmod.unsigned (N.v58512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58512 s i)) at 1.
  unfold R.v58512, N.v58512.
  rewrite ?node_58510.
  rewrite ?node_58511.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58513 (s : N.State) (i : N.Inputs) :
  R.v58513 (state s) (inputs i) = Zmod.unsigned (N.v58513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58513 s i)) at 1.
  unfold R.v58513, N.v58513.
  unfold R.v16463, N.v16463.
  rewrite ?node_58512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58514 (s : N.State) (i : N.Inputs) :
  R.v58514 (state s) (inputs i) = Zmod.unsigned (N.v58514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58514 s i)) at 1.
  unfold R.v58514, N.v58514.
  rewrite ?node_15722.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58515 (s : N.State) (i : N.Inputs) :
  R.v58515 (state s) (inputs i) = Zmod.unsigned (N.v58515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58515 s i)) at 1.
  unfold R.v58515, N.v58515.
  unfold R.v6, N.v6.
  rewrite ?node_15772.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58516 (s : N.State) (i : N.Inputs) :
  R.v58516 (state s) (inputs i) = Zmod.unsigned (N.v58516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58516 s i)) at 1.
  unfold R.v58516, N.v58516.
  rewrite ?node_58514.
  rewrite ?node_58515.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58517 (s : N.State) (i : N.Inputs) :
  R.v58517 (state s) (inputs i) = Zmod.unsigned (N.v58517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58517 s i)) at 1.
  unfold R.v58517, N.v58517.
  rewrite ?node_58513.
  rewrite ?node_58516.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58518 (s : N.State) (i : N.Inputs) :
  R.v58518 (state s) (inputs i) = Zmod.unsigned (N.v58518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58518 s i)) at 1.
  unfold R.v58518, N.v58518.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58519 (s : N.State) (i : N.Inputs) :
  R.v58519 (state s) (inputs i) = Zmod.unsigned (N.v58519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58519 s i)) at 1.
  unfold R.v58519, N.v58519.
  unfold R.v6, N.v6.
  rewrite ?node_15769.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58520 (s : N.State) (i : N.Inputs) :
  R.v58520 (state s) (inputs i) = Zmod.unsigned (N.v58520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58520 s i)) at 1.
  unfold R.v58520, N.v58520.
  unfold R.v6, N.v6.
  rewrite ?node_15768.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58521 (s : N.State) (i : N.Inputs) :
  R.v58521 (state s) (inputs i) = Zmod.unsigned (N.v58521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58521 s i)) at 1.
  unfold R.v58521, N.v58521.
  rewrite ?node_58519.
  rewrite ?node_58520.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58522 (s : N.State) (i : N.Inputs) :
  R.v58522 (state s) (inputs i) = Zmod.unsigned (N.v58522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58522 s i)) at 1.
  unfold R.v58522, N.v58522.
  unfold R.v16463, N.v16463.
  rewrite ?node_58521.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58523 (s : N.State) (i : N.Inputs) :
  R.v58523 (state s) (inputs i) = Zmod.unsigned (N.v58523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58523 s i)) at 1.
  unfold R.v58523, N.v58523.
  rewrite ?node_15770.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58524 (s : N.State) (i : N.Inputs) :
  R.v58524 (state s) (inputs i) = Zmod.unsigned (N.v58524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58524 s i)) at 1.
  unfold R.v58524, N.v58524.
  unfold R.v6, N.v6.
  rewrite ?node_15819.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58525 (s : N.State) (i : N.Inputs) :
  R.v58525 (state s) (inputs i) = Zmod.unsigned (N.v58525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58525 s i)) at 1.
  unfold R.v58525, N.v58525.
  rewrite ?node_58523.
  rewrite ?node_58524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58526 (s : N.State) (i : N.Inputs) :
  R.v58526 (state s) (inputs i) = Zmod.unsigned (N.v58526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58526 s i)) at 1.
  unfold R.v58526, N.v58526.
  rewrite ?node_58522.
  rewrite ?node_58525.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58527 (s : N.State) (i : N.Inputs) :
  R.v58527 (state s) (inputs i) = Zmod.unsigned (N.v58527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58527 s i)) at 1.
  unfold R.v58527, N.v58527.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58528 (s : N.State) (i : N.Inputs) :
  R.v58528 (state s) (inputs i) = Zmod.unsigned (N.v58528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58528 s i)) at 1.
  unfold R.v58528, N.v58528.
  unfold R.v6, N.v6.
  rewrite ?node_15816.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58529 (s : N.State) (i : N.Inputs) :
  R.v58529 (state s) (inputs i) = Zmod.unsigned (N.v58529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58529 s i)) at 1.
  unfold R.v58529, N.v58529.
  unfold R.v6, N.v6.
  rewrite ?node_15815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58530 (s : N.State) (i : N.Inputs) :
  R.v58530 (state s) (inputs i) = Zmod.unsigned (N.v58530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58530 s i)) at 1.
  unfold R.v58530, N.v58530.
  rewrite ?node_58528.
  rewrite ?node_58529.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58531 (s : N.State) (i : N.Inputs) :
  R.v58531 (state s) (inputs i) = Zmod.unsigned (N.v58531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58531 s i)) at 1.
  unfold R.v58531, N.v58531.
  unfold R.v16463, N.v16463.
  rewrite ?node_58530.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58532 (s : N.State) (i : N.Inputs) :
  R.v58532 (state s) (inputs i) = Zmod.unsigned (N.v58532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58532 s i)) at 1.
  unfold R.v58532, N.v58532.
  rewrite ?node_15817.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58533 (s : N.State) (i : N.Inputs) :
  R.v58533 (state s) (inputs i) = Zmod.unsigned (N.v58533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58533 s i)) at 1.
  unfold R.v58533, N.v58533.
  unfold R.v6, N.v6.
  rewrite ?node_15862.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58534 (s : N.State) (i : N.Inputs) :
  R.v58534 (state s) (inputs i) = Zmod.unsigned (N.v58534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58534 s i)) at 1.
  unfold R.v58534, N.v58534.
  rewrite ?node_58532.
  rewrite ?node_58533.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58535 (s : N.State) (i : N.Inputs) :
  R.v58535 (state s) (inputs i) = Zmod.unsigned (N.v58535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58535 s i)) at 1.
  unfold R.v58535, N.v58535.
  rewrite ?node_58531.
  rewrite ?node_58534.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58536 (s : N.State) (i : N.Inputs) :
  R.v58536 (state s) (inputs i) = Zmod.unsigned (N.v58536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58536 s i)) at 1.
  unfold R.v58536, N.v58536.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58537 (s : N.State) (i : N.Inputs) :
  R.v58537 (state s) (inputs i) = Zmod.unsigned (N.v58537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58537 s i)) at 1.
  unfold R.v58537, N.v58537.
  unfold R.v6, N.v6.
  rewrite ?node_15859.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58538 (s : N.State) (i : N.Inputs) :
  R.v58538 (state s) (inputs i) = Zmod.unsigned (N.v58538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58538 s i)) at 1.
  unfold R.v58538, N.v58538.
  unfold R.v6, N.v6.
  rewrite ?node_15858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58539 (s : N.State) (i : N.Inputs) :
  R.v58539 (state s) (inputs i) = Zmod.unsigned (N.v58539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58539 s i)) at 1.
  unfold R.v58539, N.v58539.
  rewrite ?node_58537.
  rewrite ?node_58538.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58540 (s : N.State) (i : N.Inputs) :
  R.v58540 (state s) (inputs i) = Zmod.unsigned (N.v58540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58540 s i)) at 1.
  unfold R.v58540, N.v58540.
  unfold R.v16463, N.v16463.
  rewrite ?node_58539.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58541 (s : N.State) (i : N.Inputs) :
  R.v58541 (state s) (inputs i) = Zmod.unsigned (N.v58541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58541 s i)) at 1.
  unfold R.v58541, N.v58541.
  rewrite ?node_15860.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58542 (s : N.State) (i : N.Inputs) :
  R.v58542 (state s) (inputs i) = Zmod.unsigned (N.v58542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58542 s i)) at 1.
  unfold R.v58542, N.v58542.
  unfold R.v6, N.v6.
  rewrite ?node_15902.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58543 (s : N.State) (i : N.Inputs) :
  R.v58543 (state s) (inputs i) = Zmod.unsigned (N.v58543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58543 s i)) at 1.
  unfold R.v58543, N.v58543.
  rewrite ?node_58541.
  rewrite ?node_58542.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58544 (s : N.State) (i : N.Inputs) :
  R.v58544 (state s) (inputs i) = Zmod.unsigned (N.v58544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58544 s i)) at 1.
  unfold R.v58544, N.v58544.
  rewrite ?node_58540.
  rewrite ?node_58543.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58545 (s : N.State) (i : N.Inputs) :
  R.v58545 (state s) (inputs i) = Zmod.unsigned (N.v58545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58545 s i)) at 1.
  unfold R.v58545, N.v58545.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58546 (s : N.State) (i : N.Inputs) :
  R.v58546 (state s) (inputs i) = Zmod.unsigned (N.v58546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58546 s i)) at 1.
  unfold R.v58546, N.v58546.
  unfold R.v6, N.v6.
  rewrite ?node_15899.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58547 (s : N.State) (i : N.Inputs) :
  R.v58547 (state s) (inputs i) = Zmod.unsigned (N.v58547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58547 s i)) at 1.
  unfold R.v58547, N.v58547.
  unfold R.v6, N.v6.
  rewrite ?node_15896.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58548 (s : N.State) (i : N.Inputs) :
  R.v58548 (state s) (inputs i) = Zmod.unsigned (N.v58548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58548 s i)) at 1.
  unfold R.v58548, N.v58548.
  rewrite ?node_58546.
  rewrite ?node_58547.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58549 (s : N.State) (i : N.Inputs) :
  R.v58549 (state s) (inputs i) = Zmod.unsigned (N.v58549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58549 s i)) at 1.
  unfold R.v58549, N.v58549.
  unfold R.v16463, N.v16463.
  rewrite ?node_58548.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58550 (s : N.State) (i : N.Inputs) :
  R.v58550 (state s) (inputs i) = Zmod.unsigned (N.v58550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58550 s i)) at 1.
  unfold R.v58550, N.v58550.
  rewrite ?node_15900.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58551 (s : N.State) (i : N.Inputs) :
  R.v58551 (state s) (inputs i) = Zmod.unsigned (N.v58551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58551 s i)) at 1.
  unfold R.v58551, N.v58551.
  unfold R.v6, N.v6.
  rewrite ?node_15938.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58552 (s : N.State) (i : N.Inputs) :
  R.v58552 (state s) (inputs i) = Zmod.unsigned (N.v58552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58552 s i)) at 1.
  unfold R.v58552, N.v58552.
  rewrite ?node_58550.
  rewrite ?node_58551.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58553 (s : N.State) (i : N.Inputs) :
  R.v58553 (state s) (inputs i) = Zmod.unsigned (N.v58553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58553 s i)) at 1.
  unfold R.v58553, N.v58553.
  rewrite ?node_58549.
  rewrite ?node_58552.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58554 (s : N.State) (i : N.Inputs) :
  R.v58554 (state s) (inputs i) = Zmod.unsigned (N.v58554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58554 s i)) at 1.
  unfold R.v58554, N.v58554.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58555 (s : N.State) (i : N.Inputs) :
  R.v58555 (state s) (inputs i) = Zmod.unsigned (N.v58555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58555 s i)) at 1.
  unfold R.v58555, N.v58555.
  unfold R.v6, N.v6.
  rewrite ?node_15935.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58556 (s : N.State) (i : N.Inputs) :
  R.v58556 (state s) (inputs i) = Zmod.unsigned (N.v58556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58556 s i)) at 1.
  unfold R.v58556, N.v58556.
  unfold R.v6, N.v6.
  rewrite ?node_15934.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58557 (s : N.State) (i : N.Inputs) :
  R.v58557 (state s) (inputs i) = Zmod.unsigned (N.v58557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58557 s i)) at 1.
  unfold R.v58557, N.v58557.
  rewrite ?node_58555.
  rewrite ?node_58556.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58558 (s : N.State) (i : N.Inputs) :
  R.v58558 (state s) (inputs i) = Zmod.unsigned (N.v58558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58558 s i)) at 1.
  unfold R.v58558, N.v58558.
  unfold R.v16463, N.v16463.
  rewrite ?node_58557.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58559 (s : N.State) (i : N.Inputs) :
  R.v58559 (state s) (inputs i) = Zmod.unsigned (N.v58559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58559 s i)) at 1.
  unfold R.v58559, N.v58559.
  rewrite ?node_15936.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58560 (s : N.State) (i : N.Inputs) :
  R.v58560 (state s) (inputs i) = Zmod.unsigned (N.v58560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58560 s i)) at 1.
  unfold R.v58560, N.v58560.
  unfold R.v6, N.v6.
  rewrite ?node_15973.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58561 (s : N.State) (i : N.Inputs) :
  R.v58561 (state s) (inputs i) = Zmod.unsigned (N.v58561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58561 s i)) at 1.
  unfold R.v58561, N.v58561.
  rewrite ?node_58559.
  rewrite ?node_58560.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58562 (s : N.State) (i : N.Inputs) :
  R.v58562 (state s) (inputs i) = Zmod.unsigned (N.v58562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58562 s i)) at 1.
  unfold R.v58562, N.v58562.
  rewrite ?node_58558.
  rewrite ?node_58561.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58563 (s : N.State) (i : N.Inputs) :
  R.v58563 (state s) (inputs i) = Zmod.unsigned (N.v58563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58563 s i)) at 1.
  unfold R.v58563, N.v58563.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58564 (s : N.State) (i : N.Inputs) :
  R.v58564 (state s) (inputs i) = Zmod.unsigned (N.v58564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58564 s i)) at 1.
  unfold R.v58564, N.v58564.
  unfold R.v6, N.v6.
  rewrite ?node_15970.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58565 (s : N.State) (i : N.Inputs) :
  R.v58565 (state s) (inputs i) = Zmod.unsigned (N.v58565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58565 s i)) at 1.
  unfold R.v58565, N.v58565.
  unfold R.v6, N.v6.
  rewrite ?node_15969.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58566 (s : N.State) (i : N.Inputs) :
  R.v58566 (state s) (inputs i) = Zmod.unsigned (N.v58566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58566 s i)) at 1.
  unfold R.v58566, N.v58566.
  rewrite ?node_58564.
  rewrite ?node_58565.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58567 (s : N.State) (i : N.Inputs) :
  R.v58567 (state s) (inputs i) = Zmod.unsigned (N.v58567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58567 s i)) at 1.
  unfold R.v58567, N.v58567.
  unfold R.v16463, N.v16463.
  rewrite ?node_58566.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58568 (s : N.State) (i : N.Inputs) :
  R.v58568 (state s) (inputs i) = Zmod.unsigned (N.v58568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58568 s i)) at 1.
  unfold R.v58568, N.v58568.
  rewrite ?node_15971.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58569 (s : N.State) (i : N.Inputs) :
  R.v58569 (state s) (inputs i) = Zmod.unsigned (N.v58569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58569 s i)) at 1.
  unfold R.v58569, N.v58569.
  unfold R.v6, N.v6.
  rewrite ?node_16004.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58570 (s : N.State) (i : N.Inputs) :
  R.v58570 (state s) (inputs i) = Zmod.unsigned (N.v58570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58570 s i)) at 1.
  unfold R.v58570, N.v58570.
  rewrite ?node_58568.
  rewrite ?node_58569.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58571 (s : N.State) (i : N.Inputs) :
  R.v58571 (state s) (inputs i) = Zmod.unsigned (N.v58571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58571 s i)) at 1.
  unfold R.v58571, N.v58571.
  rewrite ?node_58567.
  rewrite ?node_58570.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58572 (s : N.State) (i : N.Inputs) :
  R.v58572 (state s) (inputs i) = Zmod.unsigned (N.v58572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58572 s i)) at 1.
  unfold R.v58572, N.v58572.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58573 (s : N.State) (i : N.Inputs) :
  R.v58573 (state s) (inputs i) = Zmod.unsigned (N.v58573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58573 s i)) at 1.
  unfold R.v58573, N.v58573.
  unfold R.v6, N.v6.
  rewrite ?node_16001.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58574 (s : N.State) (i : N.Inputs) :
  R.v58574 (state s) (inputs i) = Zmod.unsigned (N.v58574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58574 s i)) at 1.
  unfold R.v58574, N.v58574.
  unfold R.v6, N.v6.
  rewrite ?node_16000.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58575 (s : N.State) (i : N.Inputs) :
  R.v58575 (state s) (inputs i) = Zmod.unsigned (N.v58575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58575 s i)) at 1.
  unfold R.v58575, N.v58575.
  rewrite ?node_58573.
  rewrite ?node_58574.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58576 (s : N.State) (i : N.Inputs) :
  R.v58576 (state s) (inputs i) = Zmod.unsigned (N.v58576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58576 s i)) at 1.
  unfold R.v58576, N.v58576.
  unfold R.v16463, N.v16463.
  rewrite ?node_58575.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58577 (s : N.State) (i : N.Inputs) :
  R.v58577 (state s) (inputs i) = Zmod.unsigned (N.v58577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58577 s i)) at 1.
  unfold R.v58577, N.v58577.
  rewrite ?node_16002.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58578 (s : N.State) (i : N.Inputs) :
  R.v58578 (state s) (inputs i) = Zmod.unsigned (N.v58578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58578 s i)) at 1.
  unfold R.v58578, N.v58578.
  unfold R.v6, N.v6.
  rewrite ?node_16034.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58579 (s : N.State) (i : N.Inputs) :
  R.v58579 (state s) (inputs i) = Zmod.unsigned (N.v58579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58579 s i)) at 1.
  unfold R.v58579, N.v58579.
  rewrite ?node_58577.
  rewrite ?node_58578.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58580 (s : N.State) (i : N.Inputs) :
  R.v58580 (state s) (inputs i) = Zmod.unsigned (N.v58580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58580 s i)) at 1.
  unfold R.v58580, N.v58580.
  rewrite ?node_58576.
  rewrite ?node_58579.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58581 (s : N.State) (i : N.Inputs) :
  R.v58581 (state s) (inputs i) = Zmod.unsigned (N.v58581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58581 s i)) at 1.
  unfold R.v58581, N.v58581.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58582 (s : N.State) (i : N.Inputs) :
  R.v58582 (state s) (inputs i) = Zmod.unsigned (N.v58582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58582 s i)) at 1.
  unfold R.v58582, N.v58582.
  unfold R.v6, N.v6.
  rewrite ?node_16031.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58583 (s : N.State) (i : N.Inputs) :
  R.v58583 (state s) (inputs i) = Zmod.unsigned (N.v58583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58583 s i)) at 1.
  unfold R.v58583, N.v58583.
  unfold R.v6, N.v6.
  rewrite ?node_16030.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58584 (s : N.State) (i : N.Inputs) :
  R.v58584 (state s) (inputs i) = Zmod.unsigned (N.v58584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58584 s i)) at 1.
  unfold R.v58584, N.v58584.
  rewrite ?node_58582.
  rewrite ?node_58583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58585 (s : N.State) (i : N.Inputs) :
  R.v58585 (state s) (inputs i) = Zmod.unsigned (N.v58585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58585 s i)) at 1.
  unfold R.v58585, N.v58585.
  unfold R.v16463, N.v16463.
  rewrite ?node_58584.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58586 (s : N.State) (i : N.Inputs) :
  R.v58586 (state s) (inputs i) = Zmod.unsigned (N.v58586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58586 s i)) at 1.
  unfold R.v58586, N.v58586.
  rewrite ?node_16032.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58587 (s : N.State) (i : N.Inputs) :
  R.v58587 (state s) (inputs i) = Zmod.unsigned (N.v58587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58587 s i)) at 1.
  unfold R.v58587, N.v58587.
  unfold R.v6, N.v6.
  rewrite ?node_16062.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58588 (s : N.State) (i : N.Inputs) :
  R.v58588 (state s) (inputs i) = Zmod.unsigned (N.v58588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58588 s i)) at 1.
  unfold R.v58588, N.v58588.
  rewrite ?node_58586.
  rewrite ?node_58587.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58589 (s : N.State) (i : N.Inputs) :
  R.v58589 (state s) (inputs i) = Zmod.unsigned (N.v58589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58589 s i)) at 1.
  unfold R.v58589, N.v58589.
  rewrite ?node_58585.
  rewrite ?node_58588.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58590 (s : N.State) (i : N.Inputs) :
  R.v58590 (state s) (inputs i) = Zmod.unsigned (N.v58590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58590 s i)) at 1.
  unfold R.v58590, N.v58590.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58591 (s : N.State) (i : N.Inputs) :
  R.v58591 (state s) (inputs i) = Zmod.unsigned (N.v58591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58591 s i)) at 1.
  unfold R.v58591, N.v58591.
  unfold R.v6, N.v6.
  rewrite ?node_16059.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58592 (s : N.State) (i : N.Inputs) :
  R.v58592 (state s) (inputs i) = Zmod.unsigned (N.v58592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58592 s i)) at 1.
  unfold R.v58592, N.v58592.
  unfold R.v6, N.v6.
  rewrite ?node_16058.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58593 (s : N.State) (i : N.Inputs) :
  R.v58593 (state s) (inputs i) = Zmod.unsigned (N.v58593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58593 s i)) at 1.
  unfold R.v58593, N.v58593.
  rewrite ?node_58591.
  rewrite ?node_58592.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58594 (s : N.State) (i : N.Inputs) :
  R.v58594 (state s) (inputs i) = Zmod.unsigned (N.v58594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58594 s i)) at 1.
  unfold R.v58594, N.v58594.
  unfold R.v16463, N.v16463.
  rewrite ?node_58593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58595 (s : N.State) (i : N.Inputs) :
  R.v58595 (state s) (inputs i) = Zmod.unsigned (N.v58595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58595 s i)) at 1.
  unfold R.v58595, N.v58595.
  rewrite ?node_16060.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58596 (s : N.State) (i : N.Inputs) :
  R.v58596 (state s) (inputs i) = Zmod.unsigned (N.v58596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58596 s i)) at 1.
  unfold R.v58596, N.v58596.
  unfold R.v6, N.v6.
  rewrite ?node_16089.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58597 (s : N.State) (i : N.Inputs) :
  R.v58597 (state s) (inputs i) = Zmod.unsigned (N.v58597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58597 s i)) at 1.
  unfold R.v58597, N.v58597.
  rewrite ?node_58595.
  rewrite ?node_58596.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58598 (s : N.State) (i : N.Inputs) :
  R.v58598 (state s) (inputs i) = Zmod.unsigned (N.v58598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58598 s i)) at 1.
  unfold R.v58598, N.v58598.
  rewrite ?node_58594.
  rewrite ?node_58597.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58599 (s : N.State) (i : N.Inputs) :
  R.v58599 (state s) (inputs i) = Zmod.unsigned (N.v58599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58599 s i)) at 1.
  unfold R.v58599, N.v58599.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58600 (s : N.State) (i : N.Inputs) :
  R.v58600 (state s) (inputs i) = Zmod.unsigned (N.v58600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58600 s i)) at 1.
  unfold R.v58600, N.v58600.
  unfold R.v6, N.v6.
  rewrite ?node_16086.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58601 (s : N.State) (i : N.Inputs) :
  R.v58601 (state s) (inputs i) = Zmod.unsigned (N.v58601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58601 s i)) at 1.
  unfold R.v58601, N.v58601.
  unfold R.v6, N.v6.
  rewrite ?node_16085.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58602 (s : N.State) (i : N.Inputs) :
  R.v58602 (state s) (inputs i) = Zmod.unsigned (N.v58602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58602 s i)) at 1.
  unfold R.v58602, N.v58602.
  rewrite ?node_58600.
  rewrite ?node_58601.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58603 (s : N.State) (i : N.Inputs) :
  R.v58603 (state s) (inputs i) = Zmod.unsigned (N.v58603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58603 s i)) at 1.
  unfold R.v58603, N.v58603.
  unfold R.v16463, N.v16463.
  rewrite ?node_58602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58604 (s : N.State) (i : N.Inputs) :
  R.v58604 (state s) (inputs i) = Zmod.unsigned (N.v58604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58604 s i)) at 1.
  unfold R.v58604, N.v58604.
  rewrite ?node_16087.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58605 (s : N.State) (i : N.Inputs) :
  R.v58605 (state s) (inputs i) = Zmod.unsigned (N.v58605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58605 s i)) at 1.
  unfold R.v58605, N.v58605.
  unfold R.v6, N.v6.
  rewrite ?node_16112.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58606 (s : N.State) (i : N.Inputs) :
  R.v58606 (state s) (inputs i) = Zmod.unsigned (N.v58606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58606 s i)) at 1.
  unfold R.v58606, N.v58606.
  rewrite ?node_58604.
  rewrite ?node_58605.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58607 (s : N.State) (i : N.Inputs) :
  R.v58607 (state s) (inputs i) = Zmod.unsigned (N.v58607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58607 s i)) at 1.
  unfold R.v58607, N.v58607.
  rewrite ?node_58603.
  rewrite ?node_58606.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58608 (s : N.State) (i : N.Inputs) :
  R.v58608 (state s) (inputs i) = Zmod.unsigned (N.v58608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58608 s i)) at 1.
  unfold R.v58608, N.v58608.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58609 (s : N.State) (i : N.Inputs) :
  R.v58609 (state s) (inputs i) = Zmod.unsigned (N.v58609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58609 s i)) at 1.
  unfold R.v58609, N.v58609.
  unfold R.v6, N.v6.
  rewrite ?node_16109.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58610 (s : N.State) (i : N.Inputs) :
  R.v58610 (state s) (inputs i) = Zmod.unsigned (N.v58610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58610 s i)) at 1.
  unfold R.v58610, N.v58610.
  unfold R.v6, N.v6.
  rewrite ?node_16108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58611 (s : N.State) (i : N.Inputs) :
  R.v58611 (state s) (inputs i) = Zmod.unsigned (N.v58611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58611 s i)) at 1.
  unfold R.v58611, N.v58611.
  rewrite ?node_58609.
  rewrite ?node_58610.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58612 (s : N.State) (i : N.Inputs) :
  R.v58612 (state s) (inputs i) = Zmod.unsigned (N.v58612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58612 s i)) at 1.
  unfold R.v58612, N.v58612.
  unfold R.v16463, N.v16463.
  rewrite ?node_58611.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58613 (s : N.State) (i : N.Inputs) :
  R.v58613 (state s) (inputs i) = Zmod.unsigned (N.v58613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58613 s i)) at 1.
  unfold R.v58613, N.v58613.
  rewrite ?node_16110.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58614 (s : N.State) (i : N.Inputs) :
  R.v58614 (state s) (inputs i) = Zmod.unsigned (N.v58614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58614 s i)) at 1.
  unfold R.v58614, N.v58614.
  unfold R.v6, N.v6.
  rewrite ?node_16132.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58615 (s : N.State) (i : N.Inputs) :
  R.v58615 (state s) (inputs i) = Zmod.unsigned (N.v58615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58615 s i)) at 1.
  unfold R.v58615, N.v58615.
  rewrite ?node_58613.
  rewrite ?node_58614.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58616 (s : N.State) (i : N.Inputs) :
  R.v58616 (state s) (inputs i) = Zmod.unsigned (N.v58616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58616 s i)) at 1.
  unfold R.v58616, N.v58616.
  rewrite ?node_58612.
  rewrite ?node_58615.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58617 (s : N.State) (i : N.Inputs) :
  R.v58617 (state s) (inputs i) = Zmod.unsigned (N.v58617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58617 s i)) at 1.
  unfold R.v58617, N.v58617.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58618 (s : N.State) (i : N.Inputs) :
  R.v58618 (state s) (inputs i) = Zmod.unsigned (N.v58618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58618 s i)) at 1.
  unfold R.v58618, N.v58618.
  unfold R.v6, N.v6.
  rewrite ?node_16129.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58619 (s : N.State) (i : N.Inputs) :
  R.v58619 (state s) (inputs i) = Zmod.unsigned (N.v58619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58619 s i)) at 1.
  unfold R.v58619, N.v58619.
  unfold R.v6, N.v6.
  rewrite ?node_16128.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58620 (s : N.State) (i : N.Inputs) :
  R.v58620 (state s) (inputs i) = Zmod.unsigned (N.v58620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58620 s i)) at 1.
  unfold R.v58620, N.v58620.
  rewrite ?node_58618.
  rewrite ?node_58619.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58621 (s : N.State) (i : N.Inputs) :
  R.v58621 (state s) (inputs i) = Zmod.unsigned (N.v58621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58621 s i)) at 1.
  unfold R.v58621, N.v58621.
  unfold R.v16463, N.v16463.
  rewrite ?node_58620.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58622 (s : N.State) (i : N.Inputs) :
  R.v58622 (state s) (inputs i) = Zmod.unsigned (N.v58622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58622 s i)) at 1.
  unfold R.v58622, N.v58622.
  rewrite ?node_16130.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58623 (s : N.State) (i : N.Inputs) :
  R.v58623 (state s) (inputs i) = Zmod.unsigned (N.v58623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58623 s i)) at 1.
  unfold R.v58623, N.v58623.
  unfold R.v6, N.v6.
  rewrite ?node_16150.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58624 (s : N.State) (i : N.Inputs) :
  R.v58624 (state s) (inputs i) = Zmod.unsigned (N.v58624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58624 s i)) at 1.
  unfold R.v58624, N.v58624.
  rewrite ?node_58622.
  rewrite ?node_58623.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58625 (s : N.State) (i : N.Inputs) :
  R.v58625 (state s) (inputs i) = Zmod.unsigned (N.v58625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58625 s i)) at 1.
  unfold R.v58625, N.v58625.
  rewrite ?node_58621.
  rewrite ?node_58624.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58626 (s : N.State) (i : N.Inputs) :
  R.v58626 (state s) (inputs i) = Zmod.unsigned (N.v58626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58626 s i)) at 1.
  unfold R.v58626, N.v58626.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58627 (s : N.State) (i : N.Inputs) :
  R.v58627 (state s) (inputs i) = Zmod.unsigned (N.v58627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58627 s i)) at 1.
  unfold R.v58627, N.v58627.
  unfold R.v6, N.v6.
  rewrite ?node_16147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58628 (s : N.State) (i : N.Inputs) :
  R.v58628 (state s) (inputs i) = Zmod.unsigned (N.v58628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58628 s i)) at 1.
  unfold R.v58628, N.v58628.
  unfold R.v6, N.v6.
  rewrite ?node_16146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58629 (s : N.State) (i : N.Inputs) :
  R.v58629 (state s) (inputs i) = Zmod.unsigned (N.v58629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58629 s i)) at 1.
  unfold R.v58629, N.v58629.
  rewrite ?node_58627.
  rewrite ?node_58628.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58630 (s : N.State) (i : N.Inputs) :
  R.v58630 (state s) (inputs i) = Zmod.unsigned (N.v58630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58630 s i)) at 1.
  unfold R.v58630, N.v58630.
  unfold R.v16463, N.v16463.
  rewrite ?node_58629.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58631 (s : N.State) (i : N.Inputs) :
  R.v58631 (state s) (inputs i) = Zmod.unsigned (N.v58631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58631 s i)) at 1.
  unfold R.v58631, N.v58631.
  rewrite ?node_16148.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58632 (s : N.State) (i : N.Inputs) :
  R.v58632 (state s) (inputs i) = Zmod.unsigned (N.v58632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58632 s i)) at 1.
  unfold R.v58632, N.v58632.
  unfold R.v6, N.v6.
  rewrite ?node_16167.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58633 (s : N.State) (i : N.Inputs) :
  R.v58633 (state s) (inputs i) = Zmod.unsigned (N.v58633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58633 s i)) at 1.
  unfold R.v58633, N.v58633.
  rewrite ?node_58631.
  rewrite ?node_58632.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58634 (s : N.State) (i : N.Inputs) :
  R.v58634 (state s) (inputs i) = Zmod.unsigned (N.v58634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58634 s i)) at 1.
  unfold R.v58634, N.v58634.
  rewrite ?node_58630.
  rewrite ?node_58633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58635 (s : N.State) (i : N.Inputs) :
  R.v58635 (state s) (inputs i) = Zmod.unsigned (N.v58635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58635 s i)) at 1.
  unfold R.v58635, N.v58635.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58636 (s : N.State) (i : N.Inputs) :
  R.v58636 (state s) (inputs i) = Zmod.unsigned (N.v58636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58636 s i)) at 1.
  unfold R.v58636, N.v58636.
  unfold R.v6, N.v6.
  rewrite ?node_16164.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58637 (s : N.State) (i : N.Inputs) :
  R.v58637 (state s) (inputs i) = Zmod.unsigned (N.v58637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58637 s i)) at 1.
  unfold R.v58637, N.v58637.
  unfold R.v6, N.v6.
  rewrite ?node_16163.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58638 (s : N.State) (i : N.Inputs) :
  R.v58638 (state s) (inputs i) = Zmod.unsigned (N.v58638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58638 s i)) at 1.
  unfold R.v58638, N.v58638.
  rewrite ?node_58636.
  rewrite ?node_58637.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58639 (s : N.State) (i : N.Inputs) :
  R.v58639 (state s) (inputs i) = Zmod.unsigned (N.v58639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58639 s i)) at 1.
  unfold R.v58639, N.v58639.
  unfold R.v16463, N.v16463.
  rewrite ?node_58638.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58640 (s : N.State) (i : N.Inputs) :
  R.v58640 (state s) (inputs i) = Zmod.unsigned (N.v58640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58640 s i)) at 1.
  unfold R.v58640, N.v58640.
  rewrite ?node_16165.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58641 (s : N.State) (i : N.Inputs) :
  R.v58641 (state s) (inputs i) = Zmod.unsigned (N.v58641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58641 s i)) at 1.
  unfold R.v58641, N.v58641.
  unfold R.v6, N.v6.
  rewrite ?node_16180.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58642 (s : N.State) (i : N.Inputs) :
  R.v58642 (state s) (inputs i) = Zmod.unsigned (N.v58642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58642 s i)) at 1.
  unfold R.v58642, N.v58642.
  rewrite ?node_58640.
  rewrite ?node_58641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58643 (s : N.State) (i : N.Inputs) :
  R.v58643 (state s) (inputs i) = Zmod.unsigned (N.v58643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58643 s i)) at 1.
  unfold R.v58643, N.v58643.
  rewrite ?node_58639.
  rewrite ?node_58642.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58644 (s : N.State) (i : N.Inputs) :
  R.v58644 (state s) (inputs i) = Zmod.unsigned (N.v58644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58644 s i)) at 1.
  unfold R.v58644, N.v58644.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58645 (s : N.State) (i : N.Inputs) :
  R.v58645 (state s) (inputs i) = Zmod.unsigned (N.v58645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58645 s i)) at 1.
  unfold R.v58645, N.v58645.
  unfold R.v6, N.v6.
  rewrite ?node_16177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58646 (s : N.State) (i : N.Inputs) :
  R.v58646 (state s) (inputs i) = Zmod.unsigned (N.v58646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58646 s i)) at 1.
  unfold R.v58646, N.v58646.
  unfold R.v6, N.v6.
  rewrite ?node_16176.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58647 (s : N.State) (i : N.Inputs) :
  R.v58647 (state s) (inputs i) = Zmod.unsigned (N.v58647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58647 s i)) at 1.
  unfold R.v58647, N.v58647.
  rewrite ?node_58645.
  rewrite ?node_58646.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58648 (s : N.State) (i : N.Inputs) :
  R.v58648 (state s) (inputs i) = Zmod.unsigned (N.v58648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58648 s i)) at 1.
  unfold R.v58648, N.v58648.
  unfold R.v16463, N.v16463.
  rewrite ?node_58647.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58649 (s : N.State) (i : N.Inputs) :
  R.v58649 (state s) (inputs i) = Zmod.unsigned (N.v58649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58649 s i)) at 1.
  unfold R.v58649, N.v58649.
  rewrite ?node_16178.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58650 (s : N.State) (i : N.Inputs) :
  R.v58650 (state s) (inputs i) = Zmod.unsigned (N.v58650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58650 s i)) at 1.
  unfold R.v58650, N.v58650.
  unfold R.v6, N.v6.
  rewrite ?node_16192.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58651 (s : N.State) (i : N.Inputs) :
  R.v58651 (state s) (inputs i) = Zmod.unsigned (N.v58651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58651 s i)) at 1.
  unfold R.v58651, N.v58651.
  rewrite ?node_58649.
  rewrite ?node_58650.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58652 (s : N.State) (i : N.Inputs) :
  R.v58652 (state s) (inputs i) = Zmod.unsigned (N.v58652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58652 s i)) at 1.
  unfold R.v58652, N.v58652.
  rewrite ?node_58648.
  rewrite ?node_58651.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58653 (s : N.State) (i : N.Inputs) :
  R.v58653 (state s) (inputs i) = Zmod.unsigned (N.v58653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58653 s i)) at 1.
  unfold R.v58653, N.v58653.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58654 (s : N.State) (i : N.Inputs) :
  R.v58654 (state s) (inputs i) = Zmod.unsigned (N.v58654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58654 s i)) at 1.
  unfold R.v58654, N.v58654.
  unfold R.v6, N.v6.
  rewrite ?node_16189.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58655 (s : N.State) (i : N.Inputs) :
  R.v58655 (state s) (inputs i) = Zmod.unsigned (N.v58655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58655 s i)) at 1.
  unfold R.v58655, N.v58655.
  unfold R.v6, N.v6.
  rewrite ?node_16188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58656 (s : N.State) (i : N.Inputs) :
  R.v58656 (state s) (inputs i) = Zmod.unsigned (N.v58656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58656 s i)) at 1.
  unfold R.v58656, N.v58656.
  rewrite ?node_58654.
  rewrite ?node_58655.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58657 (s : N.State) (i : N.Inputs) :
  R.v58657 (state s) (inputs i) = Zmod.unsigned (N.v58657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58657 s i)) at 1.
  unfold R.v58657, N.v58657.
  unfold R.v16463, N.v16463.
  rewrite ?node_58656.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58658 (s : N.State) (i : N.Inputs) :
  R.v58658 (state s) (inputs i) = Zmod.unsigned (N.v58658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58658 s i)) at 1.
  unfold R.v58658, N.v58658.
  rewrite ?node_16190.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58659 (s : N.State) (i : N.Inputs) :
  R.v58659 (state s) (inputs i) = Zmod.unsigned (N.v58659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58659 s i)) at 1.
  unfold R.v58659, N.v58659.
  rewrite ?node_16188.
  rewrite ?node_16189.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58660 (s : N.State) (i : N.Inputs) :
  R.v58660 (state s) (inputs i) = Zmod.unsigned (N.v58660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58660 s i)) at 1.
  unfold R.v58660, N.v58660.
  unfold R.v6, N.v6.
  unfold R.v16463, N.v16463.
  rewrite ?node_58659.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58661 (s : N.State) (i : N.Inputs) :
  R.v58661 (state s) (inputs i) = Zmod.unsigned (N.v58661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58661 s i)) at 1.
  unfold R.v58661, N.v58661.
  rewrite ?node_58658.
  rewrite ?node_58660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58662 (s : N.State) (i : N.Inputs) :
  R.v58662 (state s) (inputs i) = Zmod.unsigned (N.v58662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58662 s i)) at 1.
  unfold R.v58662, N.v58662.
  rewrite ?node_58657.
  rewrite ?node_58661.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58663 (s : N.State) (i : N.Inputs) :
  R.v58663 (state s) (inputs i) = Zmod.unsigned (N.v58663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58663 s i)) at 1.
  unfold R.v58663, N.v58663.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58664 (s : N.State) (i : N.Inputs) :
  R.v58664 (state s) (inputs i) = Zmod.unsigned (N.v58664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58664 s i)) at 1.
  unfold R.v58664, N.v58664.
  unfold R.v6, N.v6.
  rewrite !state_r2284_nr_5F2315.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2284_nr_5F2315 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58665 (s : N.State) (i : N.Inputs) :
  R.v58665 (state s) (inputs i) = Zmod.unsigned (N.v58665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58665 s i)) at 1.
  unfold R.v58665, N.v58665.
  unfold R.v6, N.v6.
  rewrite !state_r2283_nr_5F2314.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2283_nr_5F2314 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58666 (s : N.State) (i : N.Inputs) :
  R.v58666 (state s) (inputs i) = Zmod.unsigned (N.v58666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58666 s i)) at 1.
  unfold R.v58666, N.v58666.
  rewrite ?node_58664.
  rewrite ?node_58665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58667 (s : N.State) (i : N.Inputs) :
  R.v58667 (state s) (inputs i) = Zmod.unsigned (N.v58667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58667 s i)) at 1.
  unfold R.v58667, N.v58667.
  unfold R.v16463, N.v16463.
  rewrite ?node_58666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58668 (s : N.State) (i : N.Inputs) :
  R.v58668 (state s) (inputs i) = Zmod.unsigned (N.v58668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58668 s i)) at 1.
  unfold R.v58668, N.v58668.
  rewrite ?node_16330.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58669 (s : N.State) (i : N.Inputs) :
  R.v58669 (state s) (inputs i) = Zmod.unsigned (N.v58669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58669 s i)) at 1.
  unfold R.v58669, N.v58669.
  unfold R.v6, N.v6.
  rewrite ?node_16457.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58670 (s : N.State) (i : N.Inputs) :
  R.v58670 (state s) (inputs i) = Zmod.unsigned (N.v58670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58670 s i)) at 1.
  unfold R.v58670, N.v58670.
  rewrite ?node_58668.
  rewrite ?node_58669.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58671 (s : N.State) (i : N.Inputs) :
  R.v58671 (state s) (inputs i) = Zmod.unsigned (N.v58671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58671 s i)) at 1.
  unfold R.v58671, N.v58671.
  rewrite ?node_58667.
  rewrite ?node_58670.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58672 (s : N.State) (i : N.Inputs) :
  R.v58672 (state s) (inputs i) = Zmod.unsigned (N.v58672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58672 s i)) at 1.
  unfold R.v58672, N.v58672.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58673 (s : N.State) (i : N.Inputs) :
  R.v58673 (state s) (inputs i) = Zmod.unsigned (N.v58673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58673 s i)) at 1.
  unfold R.v58673, N.v58673.
  unfold R.v6, N.v6.
  rewrite !state_r2286_nr_5F2317.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2286_nr_5F2317 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58674 (s : N.State) (i : N.Inputs) :
  R.v58674 (state s) (inputs i) = Zmod.unsigned (N.v58674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58674 s i)) at 1.
  unfold R.v58674, N.v58674.
  unfold R.v6, N.v6.
  rewrite !state_r2285_nr_5F2316.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2285_nr_5F2316 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58675 (s : N.State) (i : N.Inputs) :
  R.v58675 (state s) (inputs i) = Zmod.unsigned (N.v58675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58675 s i)) at 1.
  unfold R.v58675, N.v58675.
  rewrite ?node_58673.
  rewrite ?node_58674.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58676 (s : N.State) (i : N.Inputs) :
  R.v58676 (state s) (inputs i) = Zmod.unsigned (N.v58676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58676 s i)) at 1.
  unfold R.v58676, N.v58676.
  unfold R.v16463, N.v16463.
  rewrite ?node_58675.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58677 (s : N.State) (i : N.Inputs) :
  R.v58677 (state s) (inputs i) = Zmod.unsigned (N.v58677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58677 s i)) at 1.
  unfold R.v58677, N.v58677.
  rewrite ?node_16329.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58678 (s : N.State) (i : N.Inputs) :
  R.v58678 (state s) (inputs i) = Zmod.unsigned (N.v58678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58678 s i)) at 1.
  unfold R.v58678, N.v58678.
  unfold R.v6, N.v6.
  rewrite ?node_16456.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58679 (s : N.State) (i : N.Inputs) :
  R.v58679 (state s) (inputs i) = Zmod.unsigned (N.v58679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58679 s i)) at 1.
  unfold R.v58679, N.v58679.
  rewrite ?node_58677.
  rewrite ?node_58678.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58680 (s : N.State) (i : N.Inputs) :
  R.v58680 (state s) (inputs i) = Zmod.unsigned (N.v58680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58680 s i)) at 1.
  unfold R.v58680, N.v58680.
  rewrite ?node_58676.
  rewrite ?node_58679.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58681 (s : N.State) (i : N.Inputs) :
  R.v58681 (state s) (inputs i) = Zmod.unsigned (N.v58681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58681 s i)) at 1.
  unfold R.v58681, N.v58681.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58682 (s : N.State) (i : N.Inputs) :
  R.v58682 (state s) (inputs i) = Zmod.unsigned (N.v58682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58682 s i)) at 1.
  unfold R.v58682, N.v58682.
  unfold R.v6, N.v6.
  rewrite !state_r2288_nr_5F2319.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2288_nr_5F2319 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58683 (s : N.State) (i : N.Inputs) :
  R.v58683 (state s) (inputs i) = Zmod.unsigned (N.v58683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58683 s i)) at 1.
  unfold R.v58683, N.v58683.
  unfold R.v6, N.v6.
  rewrite !state_r2287_nr_5F2318.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2287_nr_5F2318 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58684 (s : N.State) (i : N.Inputs) :
  R.v58684 (state s) (inputs i) = Zmod.unsigned (N.v58684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58684 s i)) at 1.
  unfold R.v58684, N.v58684.
  rewrite ?node_58682.
  rewrite ?node_58683.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58685 (s : N.State) (i : N.Inputs) :
  R.v58685 (state s) (inputs i) = Zmod.unsigned (N.v58685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58685 s i)) at 1.
  unfold R.v58685, N.v58685.
  unfold R.v16463, N.v16463.
  rewrite ?node_58684.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58686 (s : N.State) (i : N.Inputs) :
  R.v58686 (state s) (inputs i) = Zmod.unsigned (N.v58686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58686 s i)) at 1.
  unfold R.v58686, N.v58686.
  rewrite ?node_16328.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58687 (s : N.State) (i : N.Inputs) :
  R.v58687 (state s) (inputs i) = Zmod.unsigned (N.v58687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58687 s i)) at 1.
  unfold R.v58687, N.v58687.
  unfold R.v6, N.v6.
  rewrite ?node_16455.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58688 (s : N.State) (i : N.Inputs) :
  R.v58688 (state s) (inputs i) = Zmod.unsigned (N.v58688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58688 s i)) at 1.
  unfold R.v58688, N.v58688.
  rewrite ?node_58686.
  rewrite ?node_58687.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58689 (s : N.State) (i : N.Inputs) :
  R.v58689 (state s) (inputs i) = Zmod.unsigned (N.v58689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58689 s i)) at 1.
  unfold R.v58689, N.v58689.
  rewrite ?node_58685.
  rewrite ?node_58688.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58690 (s : N.State) (i : N.Inputs) :
  R.v58690 (state s) (inputs i) = Zmod.unsigned (N.v58690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58690 s i)) at 1.
  unfold R.v58690, N.v58690.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58691 (s : N.State) (i : N.Inputs) :
  R.v58691 (state s) (inputs i) = Zmod.unsigned (N.v58691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58691 s i)) at 1.
  unfold R.v58691, N.v58691.
  unfold R.v6, N.v6.
  rewrite !state_r2290_nr_5F2321.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2290_nr_5F2321 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58692 (s : N.State) (i : N.Inputs) :
  R.v58692 (state s) (inputs i) = Zmod.unsigned (N.v58692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58692 s i)) at 1.
  unfold R.v58692, N.v58692.
  unfold R.v6, N.v6.
  rewrite !state_r2289_nr_5F2320.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2289_nr_5F2320 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58693 (s : N.State) (i : N.Inputs) :
  R.v58693 (state s) (inputs i) = Zmod.unsigned (N.v58693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58693 s i)) at 1.
  unfold R.v58693, N.v58693.
  rewrite ?node_58691.
  rewrite ?node_58692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58694 (s : N.State) (i : N.Inputs) :
  R.v58694 (state s) (inputs i) = Zmod.unsigned (N.v58694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58694 s i)) at 1.
  unfold R.v58694, N.v58694.
  unfold R.v16463, N.v16463.
  rewrite ?node_58693.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58695 (s : N.State) (i : N.Inputs) :
  R.v58695 (state s) (inputs i) = Zmod.unsigned (N.v58695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58695 s i)) at 1.
  unfold R.v58695, N.v58695.
  rewrite ?node_16327.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58696 (s : N.State) (i : N.Inputs) :
  R.v58696 (state s) (inputs i) = Zmod.unsigned (N.v58696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58696 s i)) at 1.
  unfold R.v58696, N.v58696.
  unfold R.v6, N.v6.
  rewrite ?node_16454.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58697 (s : N.State) (i : N.Inputs) :
  R.v58697 (state s) (inputs i) = Zmod.unsigned (N.v58697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58697 s i)) at 1.
  unfold R.v58697, N.v58697.
  rewrite ?node_58695.
  rewrite ?node_58696.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58698 (s : N.State) (i : N.Inputs) :
  R.v58698 (state s) (inputs i) = Zmod.unsigned (N.v58698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58698 s i)) at 1.
  unfold R.v58698, N.v58698.
  rewrite ?node_58694.
  rewrite ?node_58697.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58699 (s : N.State) (i : N.Inputs) :
  R.v58699 (state s) (inputs i) = Zmod.unsigned (N.v58699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58699 s i)) at 1.
  unfold R.v58699, N.v58699.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58700 (s : N.State) (i : N.Inputs) :
  R.v58700 (state s) (inputs i) = Zmod.unsigned (N.v58700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58700 s i)) at 1.
  unfold R.v58700, N.v58700.
  unfold R.v6, N.v6.
  rewrite !state_r2292_nr_5F2323.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2292_nr_5F2323 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58701 (s : N.State) (i : N.Inputs) :
  R.v58701 (state s) (inputs i) = Zmod.unsigned (N.v58701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58701 s i)) at 1.
  unfold R.v58701, N.v58701.
  unfold R.v6, N.v6.
  rewrite !state_r2291_nr_5F2322.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2291_nr_5F2322 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58702 (s : N.State) (i : N.Inputs) :
  R.v58702 (state s) (inputs i) = Zmod.unsigned (N.v58702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58702 s i)) at 1.
  unfold R.v58702, N.v58702.
  rewrite ?node_58700.
  rewrite ?node_58701.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58703 (s : N.State) (i : N.Inputs) :
  R.v58703 (state s) (inputs i) = Zmod.unsigned (N.v58703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58703 s i)) at 1.
  unfold R.v58703, N.v58703.
  unfold R.v16463, N.v16463.
  rewrite ?node_58702.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58704 (s : N.State) (i : N.Inputs) :
  R.v58704 (state s) (inputs i) = Zmod.unsigned (N.v58704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58704 s i)) at 1.
  unfold R.v58704, N.v58704.
  rewrite ?node_16326.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58705 (s : N.State) (i : N.Inputs) :
  R.v58705 (state s) (inputs i) = Zmod.unsigned (N.v58705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58705 s i)) at 1.
  unfold R.v58705, N.v58705.
  unfold R.v6, N.v6.
  rewrite ?node_16453.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58706 (s : N.State) (i : N.Inputs) :
  R.v58706 (state s) (inputs i) = Zmod.unsigned (N.v58706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58706 s i)) at 1.
  unfold R.v58706, N.v58706.
  rewrite ?node_58704.
  rewrite ?node_58705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58707 (s : N.State) (i : N.Inputs) :
  R.v58707 (state s) (inputs i) = Zmod.unsigned (N.v58707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58707 s i)) at 1.
  unfold R.v58707, N.v58707.
  rewrite ?node_58703.
  rewrite ?node_58706.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58708 (s : N.State) (i : N.Inputs) :
  R.v58708 (state s) (inputs i) = Zmod.unsigned (N.v58708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58708 s i)) at 1.
  unfold R.v58708, N.v58708.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58709 (s : N.State) (i : N.Inputs) :
  R.v58709 (state s) (inputs i) = Zmod.unsigned (N.v58709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58709 s i)) at 1.
  unfold R.v58709, N.v58709.
  unfold R.v6, N.v6.
  rewrite !state_r2294_nr_5F2325.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2294_nr_5F2325 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58710 (s : N.State) (i : N.Inputs) :
  R.v58710 (state s) (inputs i) = Zmod.unsigned (N.v58710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58710 s i)) at 1.
  unfold R.v58710, N.v58710.
  unfold R.v6, N.v6.
  rewrite !state_r2293_nr_5F2324.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2293_nr_5F2324 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58711 (s : N.State) (i : N.Inputs) :
  R.v58711 (state s) (inputs i) = Zmod.unsigned (N.v58711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58711 s i)) at 1.
  unfold R.v58711, N.v58711.
  rewrite ?node_58709.
  rewrite ?node_58710.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58712 (s : N.State) (i : N.Inputs) :
  R.v58712 (state s) (inputs i) = Zmod.unsigned (N.v58712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58712 s i)) at 1.
  unfold R.v58712, N.v58712.
  unfold R.v16463, N.v16463.
  rewrite ?node_58711.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58713 (s : N.State) (i : N.Inputs) :
  R.v58713 (state s) (inputs i) = Zmod.unsigned (N.v58713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58713 s i)) at 1.
  unfold R.v58713, N.v58713.
  rewrite ?node_16325.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58714 (s : N.State) (i : N.Inputs) :
  R.v58714 (state s) (inputs i) = Zmod.unsigned (N.v58714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58714 s i)) at 1.
  unfold R.v58714, N.v58714.
  unfold R.v6, N.v6.
  rewrite ?node_16452.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58715 (s : N.State) (i : N.Inputs) :
  R.v58715 (state s) (inputs i) = Zmod.unsigned (N.v58715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58715 s i)) at 1.
  unfold R.v58715, N.v58715.
  rewrite ?node_58713.
  rewrite ?node_58714.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58716 (s : N.State) (i : N.Inputs) :
  R.v58716 (state s) (inputs i) = Zmod.unsigned (N.v58716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58716 s i)) at 1.
  unfold R.v58716, N.v58716.
  rewrite ?node_58712.
  rewrite ?node_58715.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58717 (s : N.State) (i : N.Inputs) :
  R.v58717 (state s) (inputs i) = Zmod.unsigned (N.v58717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58717 s i)) at 1.
  unfold R.v58717, N.v58717.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58718 (s : N.State) (i : N.Inputs) :
  R.v58718 (state s) (inputs i) = Zmod.unsigned (N.v58718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58718 s i)) at 1.
  unfold R.v58718, N.v58718.
  unfold R.v6, N.v6.
  rewrite !state_r2296_nr_5F2327.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2296_nr_5F2327 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58719 (s : N.State) (i : N.Inputs) :
  R.v58719 (state s) (inputs i) = Zmod.unsigned (N.v58719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58719 s i)) at 1.
  unfold R.v58719, N.v58719.
  unfold R.v6, N.v6.
  rewrite !state_r2295_nr_5F2326.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2295_nr_5F2326 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58720 (s : N.State) (i : N.Inputs) :
  R.v58720 (state s) (inputs i) = Zmod.unsigned (N.v58720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58720 s i)) at 1.
  unfold R.v58720, N.v58720.
  rewrite ?node_58718.
  rewrite ?node_58719.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58721 (s : N.State) (i : N.Inputs) :
  R.v58721 (state s) (inputs i) = Zmod.unsigned (N.v58721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58721 s i)) at 1.
  unfold R.v58721, N.v58721.
  unfold R.v16463, N.v16463.
  rewrite ?node_58720.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58722 (s : N.State) (i : N.Inputs) :
  R.v58722 (state s) (inputs i) = Zmod.unsigned (N.v58722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58722 s i)) at 1.
  unfold R.v58722, N.v58722.
  rewrite ?node_16324.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58723 (s : N.State) (i : N.Inputs) :
  R.v58723 (state s) (inputs i) = Zmod.unsigned (N.v58723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58723 s i)) at 1.
  unfold R.v58723, N.v58723.
  unfold R.v6, N.v6.
  rewrite ?node_16451.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58724 (s : N.State) (i : N.Inputs) :
  R.v58724 (state s) (inputs i) = Zmod.unsigned (N.v58724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58724 s i)) at 1.
  unfold R.v58724, N.v58724.
  rewrite ?node_58722.
  rewrite ?node_58723.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58725 (s : N.State) (i : N.Inputs) :
  R.v58725 (state s) (inputs i) = Zmod.unsigned (N.v58725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58725 s i)) at 1.
  unfold R.v58725, N.v58725.
  rewrite ?node_58721.
  rewrite ?node_58724.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58726 (s : N.State) (i : N.Inputs) :
  R.v58726 (state s) (inputs i) = Zmod.unsigned (N.v58726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58726 s i)) at 1.
  unfold R.v58726, N.v58726.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58727 (s : N.State) (i : N.Inputs) :
  R.v58727 (state s) (inputs i) = Zmod.unsigned (N.v58727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58727 s i)) at 1.
  unfold R.v58727, N.v58727.
  unfold R.v6, N.v6.
  rewrite !state_r2298_nr_5F2329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2298_nr_5F2329 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58728 (s : N.State) (i : N.Inputs) :
  R.v58728 (state s) (inputs i) = Zmod.unsigned (N.v58728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58728 s i)) at 1.
  unfold R.v58728, N.v58728.
  unfold R.v6, N.v6.
  rewrite !state_r2297_nr_5F2328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2297_nr_5F2328 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58729 (s : N.State) (i : N.Inputs) :
  R.v58729 (state s) (inputs i) = Zmod.unsigned (N.v58729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58729 s i)) at 1.
  unfold R.v58729, N.v58729.
  rewrite ?node_58727.
  rewrite ?node_58728.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58730 (s : N.State) (i : N.Inputs) :
  R.v58730 (state s) (inputs i) = Zmod.unsigned (N.v58730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58730 s i)) at 1.
  unfold R.v58730, N.v58730.
  unfold R.v16463, N.v16463.
  rewrite ?node_58729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58731 (s : N.State) (i : N.Inputs) :
  R.v58731 (state s) (inputs i) = Zmod.unsigned (N.v58731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58731 s i)) at 1.
  unfold R.v58731, N.v58731.
  rewrite ?node_16323.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58732 (s : N.State) (i : N.Inputs) :
  R.v58732 (state s) (inputs i) = Zmod.unsigned (N.v58732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58732 s i)) at 1.
  unfold R.v58732, N.v58732.
  unfold R.v6, N.v6.
  rewrite ?node_16450.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58733 (s : N.State) (i : N.Inputs) :
  R.v58733 (state s) (inputs i) = Zmod.unsigned (N.v58733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58733 s i)) at 1.
  unfold R.v58733, N.v58733.
  rewrite ?node_58731.
  rewrite ?node_58732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58734 (s : N.State) (i : N.Inputs) :
  R.v58734 (state s) (inputs i) = Zmod.unsigned (N.v58734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58734 s i)) at 1.
  unfold R.v58734, N.v58734.
  rewrite ?node_58730.
  rewrite ?node_58733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58735 (s : N.State) (i : N.Inputs) :
  R.v58735 (state s) (inputs i) = Zmod.unsigned (N.v58735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58735 s i)) at 1.
  unfold R.v58735, N.v58735.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58736 (s : N.State) (i : N.Inputs) :
  R.v58736 (state s) (inputs i) = Zmod.unsigned (N.v58736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58736 s i)) at 1.
  unfold R.v58736, N.v58736.
  unfold R.v6, N.v6.
  rewrite !state_r2300_nr_5F2331.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2300_nr_5F2331 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58737 (s : N.State) (i : N.Inputs) :
  R.v58737 (state s) (inputs i) = Zmod.unsigned (N.v58737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58737 s i)) at 1.
  unfold R.v58737, N.v58737.
  unfold R.v6, N.v6.
  rewrite !state_r2299_nr_5F2330.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2299_nr_5F2330 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58738 (s : N.State) (i : N.Inputs) :
  R.v58738 (state s) (inputs i) = Zmod.unsigned (N.v58738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58738 s i)) at 1.
  unfold R.v58738, N.v58738.
  rewrite ?node_58736.
  rewrite ?node_58737.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58739 (s : N.State) (i : N.Inputs) :
  R.v58739 (state s) (inputs i) = Zmod.unsigned (N.v58739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58739 s i)) at 1.
  unfold R.v58739, N.v58739.
  unfold R.v16463, N.v16463.
  rewrite ?node_58738.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58740 (s : N.State) (i : N.Inputs) :
  R.v58740 (state s) (inputs i) = Zmod.unsigned (N.v58740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58740 s i)) at 1.
  unfold R.v58740, N.v58740.
  rewrite ?node_16322.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58741 (s : N.State) (i : N.Inputs) :
  R.v58741 (state s) (inputs i) = Zmod.unsigned (N.v58741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58741 s i)) at 1.
  unfold R.v58741, N.v58741.
  unfold R.v6, N.v6.
  rewrite ?node_16449.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58742 (s : N.State) (i : N.Inputs) :
  R.v58742 (state s) (inputs i) = Zmod.unsigned (N.v58742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58742 s i)) at 1.
  unfold R.v58742, N.v58742.
  rewrite ?node_58740.
  rewrite ?node_58741.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58743 (s : N.State) (i : N.Inputs) :
  R.v58743 (state s) (inputs i) = Zmod.unsigned (N.v58743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58743 s i)) at 1.
  unfold R.v58743, N.v58743.
  rewrite ?node_58739.
  rewrite ?node_58742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58744 (s : N.State) (i : N.Inputs) :
  R.v58744 (state s) (inputs i) = Zmod.unsigned (N.v58744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58744 s i)) at 1.
  unfold R.v58744, N.v58744.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58745 (s : N.State) (i : N.Inputs) :
  R.v58745 (state s) (inputs i) = Zmod.unsigned (N.v58745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58745 s i)) at 1.
  unfold R.v58745, N.v58745.
  unfold R.v6, N.v6.
  rewrite !state_r2302_nr_5F2333.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2302_nr_5F2333 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58746 (s : N.State) (i : N.Inputs) :
  R.v58746 (state s) (inputs i) = Zmod.unsigned (N.v58746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58746 s i)) at 1.
  unfold R.v58746, N.v58746.
  unfold R.v6, N.v6.
  rewrite !state_r2301_nr_5F2332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2301_nr_5F2332 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58747 (s : N.State) (i : N.Inputs) :
  R.v58747 (state s) (inputs i) = Zmod.unsigned (N.v58747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58747 s i)) at 1.
  unfold R.v58747, N.v58747.
  rewrite ?node_58745.
  rewrite ?node_58746.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58748 (s : N.State) (i : N.Inputs) :
  R.v58748 (state s) (inputs i) = Zmod.unsigned (N.v58748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58748 s i)) at 1.
  unfold R.v58748, N.v58748.
  unfold R.v16463, N.v16463.
  rewrite ?node_58747.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58749 (s : N.State) (i : N.Inputs) :
  R.v58749 (state s) (inputs i) = Zmod.unsigned (N.v58749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58749 s i)) at 1.
  unfold R.v58749, N.v58749.
  rewrite ?node_16321.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58750 (s : N.State) (i : N.Inputs) :
  R.v58750 (state s) (inputs i) = Zmod.unsigned (N.v58750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58750 s i)) at 1.
  unfold R.v58750, N.v58750.
  unfold R.v6, N.v6.
  rewrite ?node_16448.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58751 (s : N.State) (i : N.Inputs) :
  R.v58751 (state s) (inputs i) = Zmod.unsigned (N.v58751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58751 s i)) at 1.
  unfold R.v58751, N.v58751.
  rewrite ?node_58749.
  rewrite ?node_58750.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58752 (s : N.State) (i : N.Inputs) :
  R.v58752 (state s) (inputs i) = Zmod.unsigned (N.v58752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58752 s i)) at 1.
  unfold R.v58752, N.v58752.
  rewrite ?node_58748.
  rewrite ?node_58751.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58753 (s : N.State) (i : N.Inputs) :
  R.v58753 (state s) (inputs i) = Zmod.unsigned (N.v58753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58753 s i)) at 1.
  unfold R.v58753, N.v58753.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58754 (s : N.State) (i : N.Inputs) :
  R.v58754 (state s) (inputs i) = Zmod.unsigned (N.v58754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58754 s i)) at 1.
  unfold R.v58754, N.v58754.
  unfold R.v6, N.v6.
  rewrite !state_r2304_nr_5F2335.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2304_nr_5F2335 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58755 (s : N.State) (i : N.Inputs) :
  R.v58755 (state s) (inputs i) = Zmod.unsigned (N.v58755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58755 s i)) at 1.
  unfold R.v58755, N.v58755.
  unfold R.v6, N.v6.
  rewrite !state_r2303_nr_5F2334.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2303_nr_5F2334 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58756 (s : N.State) (i : N.Inputs) :
  R.v58756 (state s) (inputs i) = Zmod.unsigned (N.v58756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58756 s i)) at 1.
  unfold R.v58756, N.v58756.
  rewrite ?node_58754.
  rewrite ?node_58755.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58757 (s : N.State) (i : N.Inputs) :
  R.v58757 (state s) (inputs i) = Zmod.unsigned (N.v58757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58757 s i)) at 1.
  unfold R.v58757, N.v58757.
  unfold R.v16463, N.v16463.
  rewrite ?node_58756.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58758 (s : N.State) (i : N.Inputs) :
  R.v58758 (state s) (inputs i) = Zmod.unsigned (N.v58758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58758 s i)) at 1.
  unfold R.v58758, N.v58758.
  rewrite ?node_16320.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58759 (s : N.State) (i : N.Inputs) :
  R.v58759 (state s) (inputs i) = Zmod.unsigned (N.v58759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58759 s i)) at 1.
  unfold R.v58759, N.v58759.
  unfold R.v6, N.v6.
  rewrite ?node_16447.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58760 (s : N.State) (i : N.Inputs) :
  R.v58760 (state s) (inputs i) = Zmod.unsigned (N.v58760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58760 s i)) at 1.
  unfold R.v58760, N.v58760.
  rewrite ?node_58758.
  rewrite ?node_58759.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58761 (s : N.State) (i : N.Inputs) :
  R.v58761 (state s) (inputs i) = Zmod.unsigned (N.v58761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58761 s i)) at 1.
  unfold R.v58761, N.v58761.
  rewrite ?node_58757.
  rewrite ?node_58760.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58762 (s : N.State) (i : N.Inputs) :
  R.v58762 (state s) (inputs i) = Zmod.unsigned (N.v58762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58762 s i)) at 1.
  unfold R.v58762, N.v58762.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58763 (s : N.State) (i : N.Inputs) :
  R.v58763 (state s) (inputs i) = Zmod.unsigned (N.v58763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58763 s i)) at 1.
  unfold R.v58763, N.v58763.
  unfold R.v6, N.v6.
  rewrite !state_r2306_nr_5F2337.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2306_nr_5F2337 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58764 (s : N.State) (i : N.Inputs) :
  R.v58764 (state s) (inputs i) = Zmod.unsigned (N.v58764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58764 s i)) at 1.
  unfold R.v58764, N.v58764.
  unfold R.v6, N.v6.
  rewrite !state_r2305_nr_5F2336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2305_nr_5F2336 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58765 (s : N.State) (i : N.Inputs) :
  R.v58765 (state s) (inputs i) = Zmod.unsigned (N.v58765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58765 s i)) at 1.
  unfold R.v58765, N.v58765.
  rewrite ?node_58763.
  rewrite ?node_58764.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58766 (s : N.State) (i : N.Inputs) :
  R.v58766 (state s) (inputs i) = Zmod.unsigned (N.v58766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58766 s i)) at 1.
  unfold R.v58766, N.v58766.
  unfold R.v16463, N.v16463.
  rewrite ?node_58765.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58767 (s : N.State) (i : N.Inputs) :
  R.v58767 (state s) (inputs i) = Zmod.unsigned (N.v58767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58767 s i)) at 1.
  unfold R.v58767, N.v58767.
  rewrite ?node_16319.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58768 (s : N.State) (i : N.Inputs) :
  R.v58768 (state s) (inputs i) = Zmod.unsigned (N.v58768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58768 s i)) at 1.
  unfold R.v58768, N.v58768.
  unfold R.v6, N.v6.
  rewrite ?node_16446.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58769 (s : N.State) (i : N.Inputs) :
  R.v58769 (state s) (inputs i) = Zmod.unsigned (N.v58769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58769 s i)) at 1.
  unfold R.v58769, N.v58769.
  rewrite ?node_58767.
  rewrite ?node_58768.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58770 (s : N.State) (i : N.Inputs) :
  R.v58770 (state s) (inputs i) = Zmod.unsigned (N.v58770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58770 s i)) at 1.
  unfold R.v58770, N.v58770.
  rewrite ?node_58766.
  rewrite ?node_58769.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58771 (s : N.State) (i : N.Inputs) :
  R.v58771 (state s) (inputs i) = Zmod.unsigned (N.v58771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58771 s i)) at 1.
  unfold R.v58771, N.v58771.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58772 (s : N.State) (i : N.Inputs) :
  R.v58772 (state s) (inputs i) = Zmod.unsigned (N.v58772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58772 s i)) at 1.
  unfold R.v58772, N.v58772.
  unfold R.v6, N.v6.
  rewrite !state_r2308_nr_5F2339.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2308_nr_5F2339 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58773 (s : N.State) (i : N.Inputs) :
  R.v58773 (state s) (inputs i) = Zmod.unsigned (N.v58773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58773 s i)) at 1.
  unfold R.v58773, N.v58773.
  unfold R.v6, N.v6.
  rewrite !state_r2307_nr_5F2338.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2307_nr_5F2338 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58774 (s : N.State) (i : N.Inputs) :
  R.v58774 (state s) (inputs i) = Zmod.unsigned (N.v58774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58774 s i)) at 1.
  unfold R.v58774, N.v58774.
  rewrite ?node_58772.
  rewrite ?node_58773.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58775 (s : N.State) (i : N.Inputs) :
  R.v58775 (state s) (inputs i) = Zmod.unsigned (N.v58775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58775 s i)) at 1.
  unfold R.v58775, N.v58775.
  unfold R.v16463, N.v16463.
  rewrite ?node_58774.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58776 (s : N.State) (i : N.Inputs) :
  R.v58776 (state s) (inputs i) = Zmod.unsigned (N.v58776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58776 s i)) at 1.
  unfold R.v58776, N.v58776.
  rewrite ?node_16318.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58777 (s : N.State) (i : N.Inputs) :
  R.v58777 (state s) (inputs i) = Zmod.unsigned (N.v58777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58777 s i)) at 1.
  unfold R.v58777, N.v58777.
  unfold R.v6, N.v6.
  rewrite ?node_16445.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58778 (s : N.State) (i : N.Inputs) :
  R.v58778 (state s) (inputs i) = Zmod.unsigned (N.v58778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58778 s i)) at 1.
  unfold R.v58778, N.v58778.
  rewrite ?node_58776.
  rewrite ?node_58777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58779 (s : N.State) (i : N.Inputs) :
  R.v58779 (state s) (inputs i) = Zmod.unsigned (N.v58779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58779 s i)) at 1.
  unfold R.v58779, N.v58779.
  rewrite ?node_58775.
  rewrite ?node_58778.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58780 (s : N.State) (i : N.Inputs) :
  R.v58780 (state s) (inputs i) = Zmod.unsigned (N.v58780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58780 s i)) at 1.
  unfold R.v58780, N.v58780.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58781 (s : N.State) (i : N.Inputs) :
  R.v58781 (state s) (inputs i) = Zmod.unsigned (N.v58781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58781 s i)) at 1.
  unfold R.v58781, N.v58781.
  unfold R.v6, N.v6.
  rewrite !state_r2310_nr_5F2341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2310_nr_5F2341 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58782 (s : N.State) (i : N.Inputs) :
  R.v58782 (state s) (inputs i) = Zmod.unsigned (N.v58782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58782 s i)) at 1.
  unfold R.v58782, N.v58782.
  unfold R.v6, N.v6.
  rewrite !state_r2309_nr_5F2340.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2309_nr_5F2340 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58783 (s : N.State) (i : N.Inputs) :
  R.v58783 (state s) (inputs i) = Zmod.unsigned (N.v58783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58783 s i)) at 1.
  unfold R.v58783, N.v58783.
  rewrite ?node_58781.
  rewrite ?node_58782.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58784 (s : N.State) (i : N.Inputs) :
  R.v58784 (state s) (inputs i) = Zmod.unsigned (N.v58784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58784 s i)) at 1.
  unfold R.v58784, N.v58784.
  unfold R.v16463, N.v16463.
  rewrite ?node_58783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58785 (s : N.State) (i : N.Inputs) :
  R.v58785 (state s) (inputs i) = Zmod.unsigned (N.v58785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58785 s i)) at 1.
  unfold R.v58785, N.v58785.
  rewrite ?node_16317.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58786 (s : N.State) (i : N.Inputs) :
  R.v58786 (state s) (inputs i) = Zmod.unsigned (N.v58786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58786 s i)) at 1.
  unfold R.v58786, N.v58786.
  unfold R.v6, N.v6.
  rewrite ?node_16444.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58787 (s : N.State) (i : N.Inputs) :
  R.v58787 (state s) (inputs i) = Zmod.unsigned (N.v58787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58787 s i)) at 1.
  unfold R.v58787, N.v58787.
  rewrite ?node_58785.
  rewrite ?node_58786.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58788 (s : N.State) (i : N.Inputs) :
  R.v58788 (state s) (inputs i) = Zmod.unsigned (N.v58788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58788 s i)) at 1.
  unfold R.v58788, N.v58788.
  rewrite ?node_58784.
  rewrite ?node_58787.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58789 (s : N.State) (i : N.Inputs) :
  R.v58789 (state s) (inputs i) = Zmod.unsigned (N.v58789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58789 s i)) at 1.
  unfold R.v58789, N.v58789.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58790 (s : N.State) (i : N.Inputs) :
  R.v58790 (state s) (inputs i) = Zmod.unsigned (N.v58790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58790 s i)) at 1.
  unfold R.v58790, N.v58790.
  unfold R.v6, N.v6.
  rewrite !state_r2312_nr_5F2343.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2312_nr_5F2343 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58791 (s : N.State) (i : N.Inputs) :
  R.v58791 (state s) (inputs i) = Zmod.unsigned (N.v58791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58791 s i)) at 1.
  unfold R.v58791, N.v58791.
  unfold R.v6, N.v6.
  rewrite !state_r2311_nr_5F2342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2311_nr_5F2342 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58792 (s : N.State) (i : N.Inputs) :
  R.v58792 (state s) (inputs i) = Zmod.unsigned (N.v58792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58792 s i)) at 1.
  unfold R.v58792, N.v58792.
  rewrite ?node_58790.
  rewrite ?node_58791.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58793 (s : N.State) (i : N.Inputs) :
  R.v58793 (state s) (inputs i) = Zmod.unsigned (N.v58793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58793 s i)) at 1.
  unfold R.v58793, N.v58793.
  unfold R.v16463, N.v16463.
  rewrite ?node_58792.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58794 (s : N.State) (i : N.Inputs) :
  R.v58794 (state s) (inputs i) = Zmod.unsigned (N.v58794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58794 s i)) at 1.
  unfold R.v58794, N.v58794.
  rewrite ?node_16316.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58795 (s : N.State) (i : N.Inputs) :
  R.v58795 (state s) (inputs i) = Zmod.unsigned (N.v58795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58795 s i)) at 1.
  unfold R.v58795, N.v58795.
  unfold R.v6, N.v6.
  rewrite ?node_16443.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58796 (s : N.State) (i : N.Inputs) :
  R.v58796 (state s) (inputs i) = Zmod.unsigned (N.v58796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58796 s i)) at 1.
  unfold R.v58796, N.v58796.
  rewrite ?node_58794.
  rewrite ?node_58795.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58797 (s : N.State) (i : N.Inputs) :
  R.v58797 (state s) (inputs i) = Zmod.unsigned (N.v58797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58797 s i)) at 1.
  unfold R.v58797, N.v58797.
  rewrite ?node_58793.
  rewrite ?node_58796.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58798 (s : N.State) (i : N.Inputs) :
  R.v58798 (state s) (inputs i) = Zmod.unsigned (N.v58798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58798 s i)) at 1.
  unfold R.v58798, N.v58798.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58799 (s : N.State) (i : N.Inputs) :
  R.v58799 (state s) (inputs i) = Zmod.unsigned (N.v58799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58799 s i)) at 1.
  unfold R.v58799, N.v58799.
  unfold R.v6, N.v6.
  rewrite !state_r2314_nr_5F2345.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2314_nr_5F2345 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58800 (s : N.State) (i : N.Inputs) :
  R.v58800 (state s) (inputs i) = Zmod.unsigned (N.v58800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58800 s i)) at 1.
  unfold R.v58800, N.v58800.
  unfold R.v6, N.v6.
  rewrite !state_r2313_nr_5F2344.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2313_nr_5F2344 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58801 (s : N.State) (i : N.Inputs) :
  R.v58801 (state s) (inputs i) = Zmod.unsigned (N.v58801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58801 s i)) at 1.
  unfold R.v58801, N.v58801.
  rewrite ?node_58799.
  rewrite ?node_58800.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58802 (s : N.State) (i : N.Inputs) :
  R.v58802 (state s) (inputs i) = Zmod.unsigned (N.v58802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58802 s i)) at 1.
  unfold R.v58802, N.v58802.
  unfold R.v16463, N.v16463.
  rewrite ?node_58801.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58803 (s : N.State) (i : N.Inputs) :
  R.v58803 (state s) (inputs i) = Zmod.unsigned (N.v58803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58803 s i)) at 1.
  unfold R.v58803, N.v58803.
  rewrite ?node_16315.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58804 (s : N.State) (i : N.Inputs) :
  R.v58804 (state s) (inputs i) = Zmod.unsigned (N.v58804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58804 s i)) at 1.
  unfold R.v58804, N.v58804.
  unfold R.v6, N.v6.
  rewrite ?node_16442.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58805 (s : N.State) (i : N.Inputs) :
  R.v58805 (state s) (inputs i) = Zmod.unsigned (N.v58805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58805 s i)) at 1.
  unfold R.v58805, N.v58805.
  rewrite ?node_58803.
  rewrite ?node_58804.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58806 (s : N.State) (i : N.Inputs) :
  R.v58806 (state s) (inputs i) = Zmod.unsigned (N.v58806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58806 s i)) at 1.
  unfold R.v58806, N.v58806.
  rewrite ?node_58802.
  rewrite ?node_58805.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58807 (s : N.State) (i : N.Inputs) :
  R.v58807 (state s) (inputs i) = Zmod.unsigned (N.v58807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58807 s i)) at 1.
  unfold R.v58807, N.v58807.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58808 (s : N.State) (i : N.Inputs) :
  R.v58808 (state s) (inputs i) = Zmod.unsigned (N.v58808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58808 s i)) at 1.
  unfold R.v58808, N.v58808.
  unfold R.v6, N.v6.
  rewrite !state_r2316_nr_5F2347.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2316_nr_5F2347 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58809 (s : N.State) (i : N.Inputs) :
  R.v58809 (state s) (inputs i) = Zmod.unsigned (N.v58809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58809 s i)) at 1.
  unfold R.v58809, N.v58809.
  unfold R.v6, N.v6.
  rewrite !state_r2315_nr_5F2346.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2315_nr_5F2346 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58810 (s : N.State) (i : N.Inputs) :
  R.v58810 (state s) (inputs i) = Zmod.unsigned (N.v58810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58810 s i)) at 1.
  unfold R.v58810, N.v58810.
  rewrite ?node_58808.
  rewrite ?node_58809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58811 (s : N.State) (i : N.Inputs) :
  R.v58811 (state s) (inputs i) = Zmod.unsigned (N.v58811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58811 s i)) at 1.
  unfold R.v58811, N.v58811.
  unfold R.v16463, N.v16463.
  rewrite ?node_58810.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58812 (s : N.State) (i : N.Inputs) :
  R.v58812 (state s) (inputs i) = Zmod.unsigned (N.v58812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58812 s i)) at 1.
  unfold R.v58812, N.v58812.
  rewrite ?node_16314.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58813 (s : N.State) (i : N.Inputs) :
  R.v58813 (state s) (inputs i) = Zmod.unsigned (N.v58813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58813 s i)) at 1.
  unfold R.v58813, N.v58813.
  unfold R.v6, N.v6.
  rewrite ?node_16441.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58814 (s : N.State) (i : N.Inputs) :
  R.v58814 (state s) (inputs i) = Zmod.unsigned (N.v58814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58814 s i)) at 1.
  unfold R.v58814, N.v58814.
  rewrite ?node_58812.
  rewrite ?node_58813.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58815 (s : N.State) (i : N.Inputs) :
  R.v58815 (state s) (inputs i) = Zmod.unsigned (N.v58815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58815 s i)) at 1.
  unfold R.v58815, N.v58815.
  rewrite ?node_58811.
  rewrite ?node_58814.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58816 (s : N.State) (i : N.Inputs) :
  R.v58816 (state s) (inputs i) = Zmod.unsigned (N.v58816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58816 s i)) at 1.
  unfold R.v58816, N.v58816.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58817 (s : N.State) (i : N.Inputs) :
  R.v58817 (state s) (inputs i) = Zmod.unsigned (N.v58817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58817 s i)) at 1.
  unfold R.v58817, N.v58817.
  unfold R.v6, N.v6.
  rewrite !state_r2318_nr_5F2349.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2318_nr_5F2349 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58818 (s : N.State) (i : N.Inputs) :
  R.v58818 (state s) (inputs i) = Zmod.unsigned (N.v58818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58818 s i)) at 1.
  unfold R.v58818, N.v58818.
  unfold R.v6, N.v6.
  rewrite !state_r2317_nr_5F2348.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2317_nr_5F2348 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58819 (s : N.State) (i : N.Inputs) :
  R.v58819 (state s) (inputs i) = Zmod.unsigned (N.v58819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58819 s i)) at 1.
  unfold R.v58819, N.v58819.
  rewrite ?node_58817.
  rewrite ?node_58818.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58820 (s : N.State) (i : N.Inputs) :
  R.v58820 (state s) (inputs i) = Zmod.unsigned (N.v58820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58820 s i)) at 1.
  unfold R.v58820, N.v58820.
  unfold R.v16463, N.v16463.
  rewrite ?node_58819.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58821 (s : N.State) (i : N.Inputs) :
  R.v58821 (state s) (inputs i) = Zmod.unsigned (N.v58821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58821 s i)) at 1.
  unfold R.v58821, N.v58821.
  rewrite ?node_16313.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58822 (s : N.State) (i : N.Inputs) :
  R.v58822 (state s) (inputs i) = Zmod.unsigned (N.v58822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58822 s i)) at 1.
  unfold R.v58822, N.v58822.
  unfold R.v6, N.v6.
  rewrite ?node_16440.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58823 (s : N.State) (i : N.Inputs) :
  R.v58823 (state s) (inputs i) = Zmod.unsigned (N.v58823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58823 s i)) at 1.
  unfold R.v58823, N.v58823.
  rewrite ?node_58821.
  rewrite ?node_58822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58824 (s : N.State) (i : N.Inputs) :
  R.v58824 (state s) (inputs i) = Zmod.unsigned (N.v58824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58824 s i)) at 1.
  unfold R.v58824, N.v58824.
  rewrite ?node_58820.
  rewrite ?node_58823.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58825 (s : N.State) (i : N.Inputs) :
  R.v58825 (state s) (inputs i) = Zmod.unsigned (N.v58825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58825 s i)) at 1.
  unfold R.v58825, N.v58825.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58826 (s : N.State) (i : N.Inputs) :
  R.v58826 (state s) (inputs i) = Zmod.unsigned (N.v58826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58826 s i)) at 1.
  unfold R.v58826, N.v58826.
  unfold R.v6, N.v6.
  rewrite !state_r2320_nr_5F2351.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2320_nr_5F2351 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58827 (s : N.State) (i : N.Inputs) :
  R.v58827 (state s) (inputs i) = Zmod.unsigned (N.v58827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58827 s i)) at 1.
  unfold R.v58827, N.v58827.
  unfold R.v6, N.v6.
  rewrite !state_r2319_nr_5F2350.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2319_nr_5F2350 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58828 (s : N.State) (i : N.Inputs) :
  R.v58828 (state s) (inputs i) = Zmod.unsigned (N.v58828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58828 s i)) at 1.
  unfold R.v58828, N.v58828.
  rewrite ?node_58826.
  rewrite ?node_58827.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58829 (s : N.State) (i : N.Inputs) :
  R.v58829 (state s) (inputs i) = Zmod.unsigned (N.v58829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58829 s i)) at 1.
  unfold R.v58829, N.v58829.
  unfold R.v16463, N.v16463.
  rewrite ?node_58828.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58830 (s : N.State) (i : N.Inputs) :
  R.v58830 (state s) (inputs i) = Zmod.unsigned (N.v58830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58830 s i)) at 1.
  unfold R.v58830, N.v58830.
  rewrite ?node_16312.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58831 (s : N.State) (i : N.Inputs) :
  R.v58831 (state s) (inputs i) = Zmod.unsigned (N.v58831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58831 s i)) at 1.
  unfold R.v58831, N.v58831.
  unfold R.v6, N.v6.
  rewrite ?node_16439.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58832 (s : N.State) (i : N.Inputs) :
  R.v58832 (state s) (inputs i) = Zmod.unsigned (N.v58832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58832 s i)) at 1.
  unfold R.v58832, N.v58832.
  rewrite ?node_58830.
  rewrite ?node_58831.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58833 (s : N.State) (i : N.Inputs) :
  R.v58833 (state s) (inputs i) = Zmod.unsigned (N.v58833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58833 s i)) at 1.
  unfold R.v58833, N.v58833.
  rewrite ?node_58829.
  rewrite ?node_58832.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58834 (s : N.State) (i : N.Inputs) :
  R.v58834 (state s) (inputs i) = Zmod.unsigned (N.v58834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58834 s i)) at 1.
  unfold R.v58834, N.v58834.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58835 (s : N.State) (i : N.Inputs) :
  R.v58835 (state s) (inputs i) = Zmod.unsigned (N.v58835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58835 s i)) at 1.
  unfold R.v58835, N.v58835.
  unfold R.v6, N.v6.
  rewrite !state_r2322_nr_5F2353.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2322_nr_5F2353 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58836 (s : N.State) (i : N.Inputs) :
  R.v58836 (state s) (inputs i) = Zmod.unsigned (N.v58836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58836 s i)) at 1.
  unfold R.v58836, N.v58836.
  unfold R.v6, N.v6.
  rewrite !state_r2321_nr_5F2352.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2321_nr_5F2352 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58837 (s : N.State) (i : N.Inputs) :
  R.v58837 (state s) (inputs i) = Zmod.unsigned (N.v58837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58837 s i)) at 1.
  unfold R.v58837, N.v58837.
  rewrite ?node_58835.
  rewrite ?node_58836.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58838 (s : N.State) (i : N.Inputs) :
  R.v58838 (state s) (inputs i) = Zmod.unsigned (N.v58838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58838 s i)) at 1.
  unfold R.v58838, N.v58838.
  unfold R.v16463, N.v16463.
  rewrite ?node_58837.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58839 (s : N.State) (i : N.Inputs) :
  R.v58839 (state s) (inputs i) = Zmod.unsigned (N.v58839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58839 s i)) at 1.
  unfold R.v58839, N.v58839.
  rewrite ?node_16311.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58840 (s : N.State) (i : N.Inputs) :
  R.v58840 (state s) (inputs i) = Zmod.unsigned (N.v58840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58840 s i)) at 1.
  unfold R.v58840, N.v58840.
  unfold R.v6, N.v6.
  rewrite ?node_16438.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58841 (s : N.State) (i : N.Inputs) :
  R.v58841 (state s) (inputs i) = Zmod.unsigned (N.v58841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58841 s i)) at 1.
  unfold R.v58841, N.v58841.
  rewrite ?node_58839.
  rewrite ?node_58840.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58842 (s : N.State) (i : N.Inputs) :
  R.v58842 (state s) (inputs i) = Zmod.unsigned (N.v58842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58842 s i)) at 1.
  unfold R.v58842, N.v58842.
  rewrite ?node_58838.
  rewrite ?node_58841.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58843 (s : N.State) (i : N.Inputs) :
  R.v58843 (state s) (inputs i) = Zmod.unsigned (N.v58843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58843 s i)) at 1.
  unfold R.v58843, N.v58843.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58844 (s : N.State) (i : N.Inputs) :
  R.v58844 (state s) (inputs i) = Zmod.unsigned (N.v58844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58844 s i)) at 1.
  unfold R.v58844, N.v58844.
  unfold R.v6, N.v6.
  rewrite !state_r2324_nr_5F2355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2324_nr_5F2355 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58845 (s : N.State) (i : N.Inputs) :
  R.v58845 (state s) (inputs i) = Zmod.unsigned (N.v58845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58845 s i)) at 1.
  unfold R.v58845, N.v58845.
  unfold R.v6, N.v6.
  rewrite !state_r2323_nr_5F2354.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2323_nr_5F2354 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58846 (s : N.State) (i : N.Inputs) :
  R.v58846 (state s) (inputs i) = Zmod.unsigned (N.v58846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58846 s i)) at 1.
  unfold R.v58846, N.v58846.
  rewrite ?node_58844.
  rewrite ?node_58845.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58847 (s : N.State) (i : N.Inputs) :
  R.v58847 (state s) (inputs i) = Zmod.unsigned (N.v58847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58847 s i)) at 1.
  unfold R.v58847, N.v58847.
  unfold R.v16463, N.v16463.
  rewrite ?node_58846.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58848 (s : N.State) (i : N.Inputs) :
  R.v58848 (state s) (inputs i) = Zmod.unsigned (N.v58848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58848 s i)) at 1.
  unfold R.v58848, N.v58848.
  rewrite ?node_16310.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58849 (s : N.State) (i : N.Inputs) :
  R.v58849 (state s) (inputs i) = Zmod.unsigned (N.v58849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58849 s i)) at 1.
  unfold R.v58849, N.v58849.
  unfold R.v6, N.v6.
  rewrite ?node_16437.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58850 (s : N.State) (i : N.Inputs) :
  R.v58850 (state s) (inputs i) = Zmod.unsigned (N.v58850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58850 s i)) at 1.
  unfold R.v58850, N.v58850.
  rewrite ?node_58848.
  rewrite ?node_58849.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58851 (s : N.State) (i : N.Inputs) :
  R.v58851 (state s) (inputs i) = Zmod.unsigned (N.v58851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58851 s i)) at 1.
  unfold R.v58851, N.v58851.
  rewrite ?node_58847.
  rewrite ?node_58850.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58852 (s : N.State) (i : N.Inputs) :
  R.v58852 (state s) (inputs i) = Zmod.unsigned (N.v58852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58852 s i)) at 1.
  unfold R.v58852, N.v58852.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58853 (s : N.State) (i : N.Inputs) :
  R.v58853 (state s) (inputs i) = Zmod.unsigned (N.v58853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58853 s i)) at 1.
  unfold R.v58853, N.v58853.
  unfold R.v6, N.v6.
  rewrite !state_r2326_nr_5F2357.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2326_nr_5F2357 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58854 (s : N.State) (i : N.Inputs) :
  R.v58854 (state s) (inputs i) = Zmod.unsigned (N.v58854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58854 s i)) at 1.
  unfold R.v58854, N.v58854.
  unfold R.v6, N.v6.
  rewrite !state_r2325_nr_5F2356.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2325_nr_5F2356 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58855 (s : N.State) (i : N.Inputs) :
  R.v58855 (state s) (inputs i) = Zmod.unsigned (N.v58855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58855 s i)) at 1.
  unfold R.v58855, N.v58855.
  rewrite ?node_58853.
  rewrite ?node_58854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58856 (s : N.State) (i : N.Inputs) :
  R.v58856 (state s) (inputs i) = Zmod.unsigned (N.v58856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58856 s i)) at 1.
  unfold R.v58856, N.v58856.
  unfold R.v16463, N.v16463.
  rewrite ?node_58855.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58857 (s : N.State) (i : N.Inputs) :
  R.v58857 (state s) (inputs i) = Zmod.unsigned (N.v58857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58857 s i)) at 1.
  unfold R.v58857, N.v58857.
  rewrite ?node_16309.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58858 (s : N.State) (i : N.Inputs) :
  R.v58858 (state s) (inputs i) = Zmod.unsigned (N.v58858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58858 s i)) at 1.
  unfold R.v58858, N.v58858.
  unfold R.v6, N.v6.
  rewrite ?node_16436.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58859 (s : N.State) (i : N.Inputs) :
  R.v58859 (state s) (inputs i) = Zmod.unsigned (N.v58859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58859 s i)) at 1.
  unfold R.v58859, N.v58859.
  rewrite ?node_58857.
  rewrite ?node_58858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58860 (s : N.State) (i : N.Inputs) :
  R.v58860 (state s) (inputs i) = Zmod.unsigned (N.v58860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58860 s i)) at 1.
  unfold R.v58860, N.v58860.
  rewrite ?node_58856.
  rewrite ?node_58859.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58861 (s : N.State) (i : N.Inputs) :
  R.v58861 (state s) (inputs i) = Zmod.unsigned (N.v58861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58861 s i)) at 1.
  unfold R.v58861, N.v58861.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58862 (s : N.State) (i : N.Inputs) :
  R.v58862 (state s) (inputs i) = Zmod.unsigned (N.v58862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58862 s i)) at 1.
  unfold R.v58862, N.v58862.
  unfold R.v6, N.v6.
  rewrite !state_r2328_nr_5F2359.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2328_nr_5F2359 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58863 (s : N.State) (i : N.Inputs) :
  R.v58863 (state s) (inputs i) = Zmod.unsigned (N.v58863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58863 s i)) at 1.
  unfold R.v58863, N.v58863.
  unfold R.v6, N.v6.
  rewrite !state_r2327_nr_5F2358.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2327_nr_5F2358 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58864 (s : N.State) (i : N.Inputs) :
  R.v58864 (state s) (inputs i) = Zmod.unsigned (N.v58864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58864 s i)) at 1.
  unfold R.v58864, N.v58864.
  rewrite ?node_58862.
  rewrite ?node_58863.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58865 (s : N.State) (i : N.Inputs) :
  R.v58865 (state s) (inputs i) = Zmod.unsigned (N.v58865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58865 s i)) at 1.
  unfold R.v58865, N.v58865.
  unfold R.v16463, N.v16463.
  rewrite ?node_58864.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58866 (s : N.State) (i : N.Inputs) :
  R.v58866 (state s) (inputs i) = Zmod.unsigned (N.v58866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58866 s i)) at 1.
  unfold R.v58866, N.v58866.
  rewrite ?node_16308.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58867 (s : N.State) (i : N.Inputs) :
  R.v58867 (state s) (inputs i) = Zmod.unsigned (N.v58867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58867 s i)) at 1.
  unfold R.v58867, N.v58867.
  unfold R.v6, N.v6.
  rewrite ?node_16435.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58868 (s : N.State) (i : N.Inputs) :
  R.v58868 (state s) (inputs i) = Zmod.unsigned (N.v58868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58868 s i)) at 1.
  unfold R.v58868, N.v58868.
  rewrite ?node_58866.
  rewrite ?node_58867.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58869 (s : N.State) (i : N.Inputs) :
  R.v58869 (state s) (inputs i) = Zmod.unsigned (N.v58869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58869 s i)) at 1.
  unfold R.v58869, N.v58869.
  rewrite ?node_58865.
  rewrite ?node_58868.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58870 (s : N.State) (i : N.Inputs) :
  R.v58870 (state s) (inputs i) = Zmod.unsigned (N.v58870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58870 s i)) at 1.
  unfold R.v58870, N.v58870.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58871 (s : N.State) (i : N.Inputs) :
  R.v58871 (state s) (inputs i) = Zmod.unsigned (N.v58871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58871 s i)) at 1.
  unfold R.v58871, N.v58871.
  unfold R.v6, N.v6.
  rewrite !state_r2330_nr_5F2361.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2330_nr_5F2361 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58872 (s : N.State) (i : N.Inputs) :
  R.v58872 (state s) (inputs i) = Zmod.unsigned (N.v58872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58872 s i)) at 1.
  unfold R.v58872, N.v58872.
  unfold R.v6, N.v6.
  rewrite !state_r2329_nr_5F2360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2329_nr_5F2360 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58873 (s : N.State) (i : N.Inputs) :
  R.v58873 (state s) (inputs i) = Zmod.unsigned (N.v58873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58873 s i)) at 1.
  unfold R.v58873, N.v58873.
  rewrite ?node_58871.
  rewrite ?node_58872.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58874 (s : N.State) (i : N.Inputs) :
  R.v58874 (state s) (inputs i) = Zmod.unsigned (N.v58874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58874 s i)) at 1.
  unfold R.v58874, N.v58874.
  unfold R.v16463, N.v16463.
  rewrite ?node_58873.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58875 (s : N.State) (i : N.Inputs) :
  R.v58875 (state s) (inputs i) = Zmod.unsigned (N.v58875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58875 s i)) at 1.
  unfold R.v58875, N.v58875.
  rewrite ?node_16307.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58876 (s : N.State) (i : N.Inputs) :
  R.v58876 (state s) (inputs i) = Zmod.unsigned (N.v58876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58876 s i)) at 1.
  unfold R.v58876, N.v58876.
  unfold R.v6, N.v6.
  rewrite ?node_16434.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58877 (s : N.State) (i : N.Inputs) :
  R.v58877 (state s) (inputs i) = Zmod.unsigned (N.v58877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58877 s i)) at 1.
  unfold R.v58877, N.v58877.
  rewrite ?node_58875.
  rewrite ?node_58876.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58878 (s : N.State) (i : N.Inputs) :
  R.v58878 (state s) (inputs i) = Zmod.unsigned (N.v58878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58878 s i)) at 1.
  unfold R.v58878, N.v58878.
  rewrite ?node_58874.
  rewrite ?node_58877.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58879 (s : N.State) (i : N.Inputs) :
  R.v58879 (state s) (inputs i) = Zmod.unsigned (N.v58879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58879 s i)) at 1.
  unfold R.v58879, N.v58879.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58880 (s : N.State) (i : N.Inputs) :
  R.v58880 (state s) (inputs i) = Zmod.unsigned (N.v58880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58880 s i)) at 1.
  unfold R.v58880, N.v58880.
  unfold R.v6, N.v6.
  rewrite !state_r2332_nr_5F2363.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2332_nr_5F2363 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58881 (s : N.State) (i : N.Inputs) :
  R.v58881 (state s) (inputs i) = Zmod.unsigned (N.v58881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58881 s i)) at 1.
  unfold R.v58881, N.v58881.
  unfold R.v6, N.v6.
  rewrite !state_r2331_nr_5F2362.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2331_nr_5F2362 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58882 (s : N.State) (i : N.Inputs) :
  R.v58882 (state s) (inputs i) = Zmod.unsigned (N.v58882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58882 s i)) at 1.
  unfold R.v58882, N.v58882.
  rewrite ?node_58880.
  rewrite ?node_58881.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58883 (s : N.State) (i : N.Inputs) :
  R.v58883 (state s) (inputs i) = Zmod.unsigned (N.v58883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58883 s i)) at 1.
  unfold R.v58883, N.v58883.
  unfold R.v16463, N.v16463.
  rewrite ?node_58882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58884 (s : N.State) (i : N.Inputs) :
  R.v58884 (state s) (inputs i) = Zmod.unsigned (N.v58884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58884 s i)) at 1.
  unfold R.v58884, N.v58884.
  rewrite ?node_16306.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58885 (s : N.State) (i : N.Inputs) :
  R.v58885 (state s) (inputs i) = Zmod.unsigned (N.v58885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58885 s i)) at 1.
  unfold R.v58885, N.v58885.
  unfold R.v6, N.v6.
  rewrite ?node_16433.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58886 (s : N.State) (i : N.Inputs) :
  R.v58886 (state s) (inputs i) = Zmod.unsigned (N.v58886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58886 s i)) at 1.
  unfold R.v58886, N.v58886.
  rewrite ?node_58884.
  rewrite ?node_58885.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58887 (s : N.State) (i : N.Inputs) :
  R.v58887 (state s) (inputs i) = Zmod.unsigned (N.v58887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58887 s i)) at 1.
  unfold R.v58887, N.v58887.
  rewrite ?node_58883.
  rewrite ?node_58886.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58888 (s : N.State) (i : N.Inputs) :
  R.v58888 (state s) (inputs i) = Zmod.unsigned (N.v58888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58888 s i)) at 1.
  unfold R.v58888, N.v58888.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58889 (s : N.State) (i : N.Inputs) :
  R.v58889 (state s) (inputs i) = Zmod.unsigned (N.v58889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58889 s i)) at 1.
  unfold R.v58889, N.v58889.
  unfold R.v6, N.v6.
  rewrite !state_r2334_nr_5F2365.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2334_nr_5F2365 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58890 (s : N.State) (i : N.Inputs) :
  R.v58890 (state s) (inputs i) = Zmod.unsigned (N.v58890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58890 s i)) at 1.
  unfold R.v58890, N.v58890.
  unfold R.v6, N.v6.
  rewrite !state_r2333_nr_5F2364.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2333_nr_5F2364 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58891 (s : N.State) (i : N.Inputs) :
  R.v58891 (state s) (inputs i) = Zmod.unsigned (N.v58891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58891 s i)) at 1.
  unfold R.v58891, N.v58891.
  rewrite ?node_58889.
  rewrite ?node_58890.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58892 (s : N.State) (i : N.Inputs) :
  R.v58892 (state s) (inputs i) = Zmod.unsigned (N.v58892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58892 s i)) at 1.
  unfold R.v58892, N.v58892.
  unfold R.v16463, N.v16463.
  rewrite ?node_58891.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58893 (s : N.State) (i : N.Inputs) :
  R.v58893 (state s) (inputs i) = Zmod.unsigned (N.v58893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58893 s i)) at 1.
  unfold R.v58893, N.v58893.
  rewrite ?node_16305.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58894 (s : N.State) (i : N.Inputs) :
  R.v58894 (state s) (inputs i) = Zmod.unsigned (N.v58894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58894 s i)) at 1.
  unfold R.v58894, N.v58894.
  unfold R.v6, N.v6.
  rewrite ?node_16432.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58895 (s : N.State) (i : N.Inputs) :
  R.v58895 (state s) (inputs i) = Zmod.unsigned (N.v58895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58895 s i)) at 1.
  unfold R.v58895, N.v58895.
  rewrite ?node_58893.
  rewrite ?node_58894.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58896 (s : N.State) (i : N.Inputs) :
  R.v58896 (state s) (inputs i) = Zmod.unsigned (N.v58896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58896 s i)) at 1.
  unfold R.v58896, N.v58896.
  rewrite ?node_58892.
  rewrite ?node_58895.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58897 (s : N.State) (i : N.Inputs) :
  R.v58897 (state s) (inputs i) = Zmod.unsigned (N.v58897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58897 s i)) at 1.
  unfold R.v58897, N.v58897.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58898 (s : N.State) (i : N.Inputs) :
  R.v58898 (state s) (inputs i) = Zmod.unsigned (N.v58898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58898 s i)) at 1.
  unfold R.v58898, N.v58898.
  unfold R.v6, N.v6.
  rewrite !state_r2336_nr_5F2367.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2336_nr_5F2367 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58899 (s : N.State) (i : N.Inputs) :
  R.v58899 (state s) (inputs i) = Zmod.unsigned (N.v58899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58899 s i)) at 1.
  unfold R.v58899, N.v58899.
  unfold R.v6, N.v6.
  rewrite !state_r2335_nr_5F2366.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2335_nr_5F2366 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58900 (s : N.State) (i : N.Inputs) :
  R.v58900 (state s) (inputs i) = Zmod.unsigned (N.v58900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58900 s i)) at 1.
  unfold R.v58900, N.v58900.
  rewrite ?node_58898.
  rewrite ?node_58899.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58901 (s : N.State) (i : N.Inputs) :
  R.v58901 (state s) (inputs i) = Zmod.unsigned (N.v58901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58901 s i)) at 1.
  unfold R.v58901, N.v58901.
  unfold R.v16463, N.v16463.
  rewrite ?node_58900.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58902 (s : N.State) (i : N.Inputs) :
  R.v58902 (state s) (inputs i) = Zmod.unsigned (N.v58902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58902 s i)) at 1.
  unfold R.v58902, N.v58902.
  rewrite ?node_16304.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58903 (s : N.State) (i : N.Inputs) :
  R.v58903 (state s) (inputs i) = Zmod.unsigned (N.v58903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58903 s i)) at 1.
  unfold R.v58903, N.v58903.
  unfold R.v6, N.v6.
  rewrite ?node_16431.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58904 (s : N.State) (i : N.Inputs) :
  R.v58904 (state s) (inputs i) = Zmod.unsigned (N.v58904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58904 s i)) at 1.
  unfold R.v58904, N.v58904.
  rewrite ?node_58902.
  rewrite ?node_58903.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58905 (s : N.State) (i : N.Inputs) :
  R.v58905 (state s) (inputs i) = Zmod.unsigned (N.v58905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58905 s i)) at 1.
  unfold R.v58905, N.v58905.
  rewrite ?node_58901.
  rewrite ?node_58904.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58906 (s : N.State) (i : N.Inputs) :
  R.v58906 (state s) (inputs i) = Zmod.unsigned (N.v58906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58906 s i)) at 1.
  unfold R.v58906, N.v58906.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58907 (s : N.State) (i : N.Inputs) :
  R.v58907 (state s) (inputs i) = Zmod.unsigned (N.v58907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58907 s i)) at 1.
  unfold R.v58907, N.v58907.
  unfold R.v6, N.v6.
  rewrite !state_r2338_nr_5F2369.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2338_nr_5F2369 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58908 (s : N.State) (i : N.Inputs) :
  R.v58908 (state s) (inputs i) = Zmod.unsigned (N.v58908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58908 s i)) at 1.
  unfold R.v58908, N.v58908.
  unfold R.v6, N.v6.
  rewrite !state_r2337_nr_5F2368.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2337_nr_5F2368 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58909 (s : N.State) (i : N.Inputs) :
  R.v58909 (state s) (inputs i) = Zmod.unsigned (N.v58909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58909 s i)) at 1.
  unfold R.v58909, N.v58909.
  rewrite ?node_58907.
  rewrite ?node_58908.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58910 (s : N.State) (i : N.Inputs) :
  R.v58910 (state s) (inputs i) = Zmod.unsigned (N.v58910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58910 s i)) at 1.
  unfold R.v58910, N.v58910.
  unfold R.v16463, N.v16463.
  rewrite ?node_58909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58911 (s : N.State) (i : N.Inputs) :
  R.v58911 (state s) (inputs i) = Zmod.unsigned (N.v58911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58911 s i)) at 1.
  unfold R.v58911, N.v58911.
  rewrite ?node_16303.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58912 (s : N.State) (i : N.Inputs) :
  R.v58912 (state s) (inputs i) = Zmod.unsigned (N.v58912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58912 s i)) at 1.
  unfold R.v58912, N.v58912.
  unfold R.v6, N.v6.
  rewrite ?node_16430.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58913 (s : N.State) (i : N.Inputs) :
  R.v58913 (state s) (inputs i) = Zmod.unsigned (N.v58913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58913 s i)) at 1.
  unfold R.v58913, N.v58913.
  rewrite ?node_58911.
  rewrite ?node_58912.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58914 (s : N.State) (i : N.Inputs) :
  R.v58914 (state s) (inputs i) = Zmod.unsigned (N.v58914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58914 s i)) at 1.
  unfold R.v58914, N.v58914.
  rewrite ?node_58910.
  rewrite ?node_58913.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58915 (s : N.State) (i : N.Inputs) :
  R.v58915 (state s) (inputs i) = Zmod.unsigned (N.v58915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58915 s i)) at 1.
  unfold R.v58915, N.v58915.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58916 (s : N.State) (i : N.Inputs) :
  R.v58916 (state s) (inputs i) = Zmod.unsigned (N.v58916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58916 s i)) at 1.
  unfold R.v58916, N.v58916.
  unfold R.v6, N.v6.
  rewrite !state_r2340_nr_5F2371.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2340_nr_5F2371 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58917 (s : N.State) (i : N.Inputs) :
  R.v58917 (state s) (inputs i) = Zmod.unsigned (N.v58917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58917 s i)) at 1.
  unfold R.v58917, N.v58917.
  unfold R.v6, N.v6.
  rewrite !state_r2339_nr_5F2370.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2339_nr_5F2370 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58918 (s : N.State) (i : N.Inputs) :
  R.v58918 (state s) (inputs i) = Zmod.unsigned (N.v58918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58918 s i)) at 1.
  unfold R.v58918, N.v58918.
  rewrite ?node_58916.
  rewrite ?node_58917.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58919 (s : N.State) (i : N.Inputs) :
  R.v58919 (state s) (inputs i) = Zmod.unsigned (N.v58919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58919 s i)) at 1.
  unfold R.v58919, N.v58919.
  unfold R.v16463, N.v16463.
  rewrite ?node_58918.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58920 (s : N.State) (i : N.Inputs) :
  R.v58920 (state s) (inputs i) = Zmod.unsigned (N.v58920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58920 s i)) at 1.
  unfold R.v58920, N.v58920.
  rewrite ?node_16302.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58921 (s : N.State) (i : N.Inputs) :
  R.v58921 (state s) (inputs i) = Zmod.unsigned (N.v58921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58921 s i)) at 1.
  unfold R.v58921, N.v58921.
  unfold R.v6, N.v6.
  rewrite ?node_16429.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58922 (s : N.State) (i : N.Inputs) :
  R.v58922 (state s) (inputs i) = Zmod.unsigned (N.v58922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58922 s i)) at 1.
  unfold R.v58922, N.v58922.
  rewrite ?node_58920.
  rewrite ?node_58921.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58923 (s : N.State) (i : N.Inputs) :
  R.v58923 (state s) (inputs i) = Zmod.unsigned (N.v58923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58923 s i)) at 1.
  unfold R.v58923, N.v58923.
  rewrite ?node_58919.
  rewrite ?node_58922.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58924 (s : N.State) (i : N.Inputs) :
  R.v58924 (state s) (inputs i) = Zmod.unsigned (N.v58924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58924 s i)) at 1.
  unfold R.v58924, N.v58924.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58925 (s : N.State) (i : N.Inputs) :
  R.v58925 (state s) (inputs i) = Zmod.unsigned (N.v58925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58925 s i)) at 1.
  unfold R.v58925, N.v58925.
  unfold R.v6, N.v6.
  rewrite !state_r2342_nr_5F2373.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2342_nr_5F2373 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58926 (s : N.State) (i : N.Inputs) :
  R.v58926 (state s) (inputs i) = Zmod.unsigned (N.v58926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58926 s i)) at 1.
  unfold R.v58926, N.v58926.
  unfold R.v6, N.v6.
  rewrite !state_r2341_nr_5F2372.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2341_nr_5F2372 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58927 (s : N.State) (i : N.Inputs) :
  R.v58927 (state s) (inputs i) = Zmod.unsigned (N.v58927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58927 s i)) at 1.
  unfold R.v58927, N.v58927.
  rewrite ?node_58925.
  rewrite ?node_58926.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58928 (s : N.State) (i : N.Inputs) :
  R.v58928 (state s) (inputs i) = Zmod.unsigned (N.v58928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58928 s i)) at 1.
  unfold R.v58928, N.v58928.
  unfold R.v16463, N.v16463.
  rewrite ?node_58927.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58929 (s : N.State) (i : N.Inputs) :
  R.v58929 (state s) (inputs i) = Zmod.unsigned (N.v58929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58929 s i)) at 1.
  unfold R.v58929, N.v58929.
  rewrite ?node_16301.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58930 (s : N.State) (i : N.Inputs) :
  R.v58930 (state s) (inputs i) = Zmod.unsigned (N.v58930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58930 s i)) at 1.
  unfold R.v58930, N.v58930.
  unfold R.v6, N.v6.
  rewrite ?node_16428.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58931 (s : N.State) (i : N.Inputs) :
  R.v58931 (state s) (inputs i) = Zmod.unsigned (N.v58931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58931 s i)) at 1.
  unfold R.v58931, N.v58931.
  rewrite ?node_58929.
  rewrite ?node_58930.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58932 (s : N.State) (i : N.Inputs) :
  R.v58932 (state s) (inputs i) = Zmod.unsigned (N.v58932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58932 s i)) at 1.
  unfold R.v58932, N.v58932.
  rewrite ?node_58928.
  rewrite ?node_58931.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58933 (s : N.State) (i : N.Inputs) :
  R.v58933 (state s) (inputs i) = Zmod.unsigned (N.v58933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58933 s i)) at 1.
  unfold R.v58933, N.v58933.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58934 (s : N.State) (i : N.Inputs) :
  R.v58934 (state s) (inputs i) = Zmod.unsigned (N.v58934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58934 s i)) at 1.
  unfold R.v58934, N.v58934.
  unfold R.v6, N.v6.
  rewrite !state_r2344_nr_5F2375.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2344_nr_5F2375 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58935 (s : N.State) (i : N.Inputs) :
  R.v58935 (state s) (inputs i) = Zmod.unsigned (N.v58935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58935 s i)) at 1.
  unfold R.v58935, N.v58935.
  unfold R.v6, N.v6.
  rewrite !state_r2343_nr_5F2374.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2343_nr_5F2374 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58936 (s : N.State) (i : N.Inputs) :
  R.v58936 (state s) (inputs i) = Zmod.unsigned (N.v58936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58936 s i)) at 1.
  unfold R.v58936, N.v58936.
  rewrite ?node_58934.
  rewrite ?node_58935.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58937 (s : N.State) (i : N.Inputs) :
  R.v58937 (state s) (inputs i) = Zmod.unsigned (N.v58937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58937 s i)) at 1.
  unfold R.v58937, N.v58937.
  unfold R.v16463, N.v16463.
  rewrite ?node_58936.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58938 (s : N.State) (i : N.Inputs) :
  R.v58938 (state s) (inputs i) = Zmod.unsigned (N.v58938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58938 s i)) at 1.
  unfold R.v58938, N.v58938.
  rewrite ?node_16300.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58939 (s : N.State) (i : N.Inputs) :
  R.v58939 (state s) (inputs i) = Zmod.unsigned (N.v58939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58939 s i)) at 1.
  unfold R.v58939, N.v58939.
  unfold R.v6, N.v6.
  rewrite ?node_16427.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58940 (s : N.State) (i : N.Inputs) :
  R.v58940 (state s) (inputs i) = Zmod.unsigned (N.v58940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58940 s i)) at 1.
  unfold R.v58940, N.v58940.
  rewrite ?node_58938.
  rewrite ?node_58939.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58941 (s : N.State) (i : N.Inputs) :
  R.v58941 (state s) (inputs i) = Zmod.unsigned (N.v58941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58941 s i)) at 1.
  unfold R.v58941, N.v58941.
  rewrite ?node_58937.
  rewrite ?node_58940.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58942 (s : N.State) (i : N.Inputs) :
  R.v58942 (state s) (inputs i) = Zmod.unsigned (N.v58942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58942 s i)) at 1.
  unfold R.v58942, N.v58942.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58943 (s : N.State) (i : N.Inputs) :
  R.v58943 (state s) (inputs i) = Zmod.unsigned (N.v58943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58943 s i)) at 1.
  unfold R.v58943, N.v58943.
  unfold R.v6, N.v6.
  rewrite !state_r2346_nr_5F2377.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2346_nr_5F2377 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58944 (s : N.State) (i : N.Inputs) :
  R.v58944 (state s) (inputs i) = Zmod.unsigned (N.v58944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58944 s i)) at 1.
  unfold R.v58944, N.v58944.
  unfold R.v6, N.v6.
  rewrite !state_r2345_nr_5F2376.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2345_nr_5F2376 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58945 (s : N.State) (i : N.Inputs) :
  R.v58945 (state s) (inputs i) = Zmod.unsigned (N.v58945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58945 s i)) at 1.
  unfold R.v58945, N.v58945.
  rewrite ?node_58943.
  rewrite ?node_58944.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58946 (s : N.State) (i : N.Inputs) :
  R.v58946 (state s) (inputs i) = Zmod.unsigned (N.v58946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58946 s i)) at 1.
  unfold R.v58946, N.v58946.
  unfold R.v16463, N.v16463.
  rewrite ?node_58945.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58947 (s : N.State) (i : N.Inputs) :
  R.v58947 (state s) (inputs i) = Zmod.unsigned (N.v58947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58947 s i)) at 1.
  unfold R.v58947, N.v58947.
  rewrite ?node_16299.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58948 (s : N.State) (i : N.Inputs) :
  R.v58948 (state s) (inputs i) = Zmod.unsigned (N.v58948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58948 s i)) at 1.
  unfold R.v58948, N.v58948.
  unfold R.v6, N.v6.
  rewrite ?node_16426.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58949 (s : N.State) (i : N.Inputs) :
  R.v58949 (state s) (inputs i) = Zmod.unsigned (N.v58949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58949 s i)) at 1.
  unfold R.v58949, N.v58949.
  rewrite ?node_58947.
  rewrite ?node_58948.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58950 (s : N.State) (i : N.Inputs) :
  R.v58950 (state s) (inputs i) = Zmod.unsigned (N.v58950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58950 s i)) at 1.
  unfold R.v58950, N.v58950.
  rewrite ?node_58946.
  rewrite ?node_58949.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58951 (s : N.State) (i : N.Inputs) :
  R.v58951 (state s) (inputs i) = Zmod.unsigned (N.v58951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58951 s i)) at 1.
  unfold R.v58951, N.v58951.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58952 (s : N.State) (i : N.Inputs) :
  R.v58952 (state s) (inputs i) = Zmod.unsigned (N.v58952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58952 s i)) at 1.
  unfold R.v58952, N.v58952.
  unfold R.v6, N.v6.
  rewrite !state_r2348_nr_5F2379.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2348_nr_5F2379 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58953 (s : N.State) (i : N.Inputs) :
  R.v58953 (state s) (inputs i) = Zmod.unsigned (N.v58953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58953 s i)) at 1.
  unfold R.v58953, N.v58953.
  unfold R.v6, N.v6.
  rewrite !state_r2347_nr_5F2378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2347_nr_5F2378 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58954 (s : N.State) (i : N.Inputs) :
  R.v58954 (state s) (inputs i) = Zmod.unsigned (N.v58954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58954 s i)) at 1.
  unfold R.v58954, N.v58954.
  rewrite ?node_58952.
  rewrite ?node_58953.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58955 (s : N.State) (i : N.Inputs) :
  R.v58955 (state s) (inputs i) = Zmod.unsigned (N.v58955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58955 s i)) at 1.
  unfold R.v58955, N.v58955.
  unfold R.v16463, N.v16463.
  rewrite ?node_58954.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58956 (s : N.State) (i : N.Inputs) :
  R.v58956 (state s) (inputs i) = Zmod.unsigned (N.v58956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58956 s i)) at 1.
  unfold R.v58956, N.v58956.
  rewrite ?node_16298.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58957 (s : N.State) (i : N.Inputs) :
  R.v58957 (state s) (inputs i) = Zmod.unsigned (N.v58957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58957 s i)) at 1.
  unfold R.v58957, N.v58957.
  unfold R.v6, N.v6.
  rewrite ?node_16425.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58958 (s : N.State) (i : N.Inputs) :
  R.v58958 (state s) (inputs i) = Zmod.unsigned (N.v58958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58958 s i)) at 1.
  unfold R.v58958, N.v58958.
  rewrite ?node_58956.
  rewrite ?node_58957.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58959 (s : N.State) (i : N.Inputs) :
  R.v58959 (state s) (inputs i) = Zmod.unsigned (N.v58959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58959 s i)) at 1.
  unfold R.v58959, N.v58959.
  rewrite ?node_58955.
  rewrite ?node_58958.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58960 (s : N.State) (i : N.Inputs) :
  R.v58960 (state s) (inputs i) = Zmod.unsigned (N.v58960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58960 s i)) at 1.
  unfold R.v58960, N.v58960.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58961 (s : N.State) (i : N.Inputs) :
  R.v58961 (state s) (inputs i) = Zmod.unsigned (N.v58961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58961 s i)) at 1.
  unfold R.v58961, N.v58961.
  unfold R.v6, N.v6.
  rewrite !state_r2350_nr_5F2381.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2350_nr_5F2381 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58962 (s : N.State) (i : N.Inputs) :
  R.v58962 (state s) (inputs i) = Zmod.unsigned (N.v58962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58962 s i)) at 1.
  unfold R.v58962, N.v58962.
  unfold R.v6, N.v6.
  rewrite !state_r2349_nr_5F2380.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2349_nr_5F2380 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58963 (s : N.State) (i : N.Inputs) :
  R.v58963 (state s) (inputs i) = Zmod.unsigned (N.v58963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58963 s i)) at 1.
  unfold R.v58963, N.v58963.
  rewrite ?node_58961.
  rewrite ?node_58962.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58964 (s : N.State) (i : N.Inputs) :
  R.v58964 (state s) (inputs i) = Zmod.unsigned (N.v58964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58964 s i)) at 1.
  unfold R.v58964, N.v58964.
  unfold R.v16463, N.v16463.
  rewrite ?node_58963.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58965 (s : N.State) (i : N.Inputs) :
  R.v58965 (state s) (inputs i) = Zmod.unsigned (N.v58965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58965 s i)) at 1.
  unfold R.v58965, N.v58965.
  rewrite ?node_16297.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58966 (s : N.State) (i : N.Inputs) :
  R.v58966 (state s) (inputs i) = Zmod.unsigned (N.v58966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58966 s i)) at 1.
  unfold R.v58966, N.v58966.
  unfold R.v6, N.v6.
  rewrite ?node_16424.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58967 (s : N.State) (i : N.Inputs) :
  R.v58967 (state s) (inputs i) = Zmod.unsigned (N.v58967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58967 s i)) at 1.
  unfold R.v58967, N.v58967.
  rewrite ?node_58965.
  rewrite ?node_58966.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58968 (s : N.State) (i : N.Inputs) :
  R.v58968 (state s) (inputs i) = Zmod.unsigned (N.v58968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58968 s i)) at 1.
  unfold R.v58968, N.v58968.
  rewrite ?node_58964.
  rewrite ?node_58967.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58969 (s : N.State) (i : N.Inputs) :
  R.v58969 (state s) (inputs i) = Zmod.unsigned (N.v58969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58969 s i)) at 1.
  unfold R.v58969, N.v58969.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58970 (s : N.State) (i : N.Inputs) :
  R.v58970 (state s) (inputs i) = Zmod.unsigned (N.v58970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58970 s i)) at 1.
  unfold R.v58970, N.v58970.
  unfold R.v6, N.v6.
  rewrite !state_r2352_nr_5F2383.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2352_nr_5F2383 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58971 (s : N.State) (i : N.Inputs) :
  R.v58971 (state s) (inputs i) = Zmod.unsigned (N.v58971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58971 s i)) at 1.
  unfold R.v58971, N.v58971.
  unfold R.v6, N.v6.
  rewrite !state_r2351_nr_5F2382.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2351_nr_5F2382 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58972 (s : N.State) (i : N.Inputs) :
  R.v58972 (state s) (inputs i) = Zmod.unsigned (N.v58972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58972 s i)) at 1.
  unfold R.v58972, N.v58972.
  rewrite ?node_58970.
  rewrite ?node_58971.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58973 (s : N.State) (i : N.Inputs) :
  R.v58973 (state s) (inputs i) = Zmod.unsigned (N.v58973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58973 s i)) at 1.
  unfold R.v58973, N.v58973.
  unfold R.v16463, N.v16463.
  rewrite ?node_58972.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58974 (s : N.State) (i : N.Inputs) :
  R.v58974 (state s) (inputs i) = Zmod.unsigned (N.v58974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58974 s i)) at 1.
  unfold R.v58974, N.v58974.
  rewrite ?node_16296.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58975 (s : N.State) (i : N.Inputs) :
  R.v58975 (state s) (inputs i) = Zmod.unsigned (N.v58975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58975 s i)) at 1.
  unfold R.v58975, N.v58975.
  unfold R.v6, N.v6.
  rewrite ?node_16423.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58976 (s : N.State) (i : N.Inputs) :
  R.v58976 (state s) (inputs i) = Zmod.unsigned (N.v58976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58976 s i)) at 1.
  unfold R.v58976, N.v58976.
  rewrite ?node_58974.
  rewrite ?node_58975.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58977 (s : N.State) (i : N.Inputs) :
  R.v58977 (state s) (inputs i) = Zmod.unsigned (N.v58977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58977 s i)) at 1.
  unfold R.v58977, N.v58977.
  rewrite ?node_58973.
  rewrite ?node_58976.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58978 (s : N.State) (i : N.Inputs) :
  R.v58978 (state s) (inputs i) = Zmod.unsigned (N.v58978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58978 s i)) at 1.
  unfold R.v58978, N.v58978.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58979 (s : N.State) (i : N.Inputs) :
  R.v58979 (state s) (inputs i) = Zmod.unsigned (N.v58979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58979 s i)) at 1.
  unfold R.v58979, N.v58979.
  unfold R.v6, N.v6.
  rewrite !state_r2354_nr_5F2385.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2354_nr_5F2385 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58980 (s : N.State) (i : N.Inputs) :
  R.v58980 (state s) (inputs i) = Zmod.unsigned (N.v58980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58980 s i)) at 1.
  unfold R.v58980, N.v58980.
  unfold R.v6, N.v6.
  rewrite !state_r2353_nr_5F2384.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2353_nr_5F2384 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58981 (s : N.State) (i : N.Inputs) :
  R.v58981 (state s) (inputs i) = Zmod.unsigned (N.v58981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58981 s i)) at 1.
  unfold R.v58981, N.v58981.
  rewrite ?node_58979.
  rewrite ?node_58980.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58982 (s : N.State) (i : N.Inputs) :
  R.v58982 (state s) (inputs i) = Zmod.unsigned (N.v58982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58982 s i)) at 1.
  unfold R.v58982, N.v58982.
  unfold R.v16463, N.v16463.
  rewrite ?node_58981.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58983 (s : N.State) (i : N.Inputs) :
  R.v58983 (state s) (inputs i) = Zmod.unsigned (N.v58983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58983 s i)) at 1.
  unfold R.v58983, N.v58983.
  rewrite ?node_16295.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58984 (s : N.State) (i : N.Inputs) :
  R.v58984 (state s) (inputs i) = Zmod.unsigned (N.v58984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58984 s i)) at 1.
  unfold R.v58984, N.v58984.
  unfold R.v6, N.v6.
  rewrite ?node_16422.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58985 (s : N.State) (i : N.Inputs) :
  R.v58985 (state s) (inputs i) = Zmod.unsigned (N.v58985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58985 s i)) at 1.
  unfold R.v58985, N.v58985.
  rewrite ?node_58983.
  rewrite ?node_58984.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58986 (s : N.State) (i : N.Inputs) :
  R.v58986 (state s) (inputs i) = Zmod.unsigned (N.v58986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58986 s i)) at 1.
  unfold R.v58986, N.v58986.
  rewrite ?node_58982.
  rewrite ?node_58985.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58987 (s : N.State) (i : N.Inputs) :
  R.v58987 (state s) (inputs i) = Zmod.unsigned (N.v58987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58987 s i)) at 1.
  unfold R.v58987, N.v58987.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58988 (s : N.State) (i : N.Inputs) :
  R.v58988 (state s) (inputs i) = Zmod.unsigned (N.v58988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58988 s i)) at 1.
  unfold R.v58988, N.v58988.
  unfold R.v6, N.v6.
  rewrite !state_r2356_nr_5F2387.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2356_nr_5F2387 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58989 (s : N.State) (i : N.Inputs) :
  R.v58989 (state s) (inputs i) = Zmod.unsigned (N.v58989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58989 s i)) at 1.
  unfold R.v58989, N.v58989.
  unfold R.v6, N.v6.
  rewrite !state_r2355_nr_5F2386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2355_nr_5F2386 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58990 (s : N.State) (i : N.Inputs) :
  R.v58990 (state s) (inputs i) = Zmod.unsigned (N.v58990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58990 s i)) at 1.
  unfold R.v58990, N.v58990.
  rewrite ?node_58988.
  rewrite ?node_58989.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58991 (s : N.State) (i : N.Inputs) :
  R.v58991 (state s) (inputs i) = Zmod.unsigned (N.v58991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58991 s i)) at 1.
  unfold R.v58991, N.v58991.
  unfold R.v16463, N.v16463.
  rewrite ?node_58990.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58992 (s : N.State) (i : N.Inputs) :
  R.v58992 (state s) (inputs i) = Zmod.unsigned (N.v58992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58992 s i)) at 1.
  unfold R.v58992, N.v58992.
  rewrite ?node_16294.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58993 (s : N.State) (i : N.Inputs) :
  R.v58993 (state s) (inputs i) = Zmod.unsigned (N.v58993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58993 s i)) at 1.
  unfold R.v58993, N.v58993.
  unfold R.v6, N.v6.
  rewrite ?node_16421.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58994 (s : N.State) (i : N.Inputs) :
  R.v58994 (state s) (inputs i) = Zmod.unsigned (N.v58994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58994 s i)) at 1.
  unfold R.v58994, N.v58994.
  rewrite ?node_58992.
  rewrite ?node_58993.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58995 (s : N.State) (i : N.Inputs) :
  R.v58995 (state s) (inputs i) = Zmod.unsigned (N.v58995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58995 s i)) at 1.
  unfold R.v58995, N.v58995.
  rewrite ?node_58991.
  rewrite ?node_58994.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58996 (s : N.State) (i : N.Inputs) :
  R.v58996 (state s) (inputs i) = Zmod.unsigned (N.v58996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58996 s i)) at 1.
  unfold R.v58996, N.v58996.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58997 (s : N.State) (i : N.Inputs) :
  R.v58997 (state s) (inputs i) = Zmod.unsigned (N.v58997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58997 s i)) at 1.
  unfold R.v58997, N.v58997.
  unfold R.v6, N.v6.
  rewrite !state_r2358_nr_5F2389.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2358_nr_5F2389 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58998 (s : N.State) (i : N.Inputs) :
  R.v58998 (state s) (inputs i) = Zmod.unsigned (N.v58998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58998 s i)) at 1.
  unfold R.v58998, N.v58998.
  unfold R.v6, N.v6.
  rewrite !state_r2357_nr_5F2388.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r2357_nr_5F2388 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_58999 (s : N.State) (i : N.Inputs) :
  R.v58999 (state s) (inputs i) = Zmod.unsigned (N.v58999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v58999 s i)) at 1.
  unfold R.v58999, N.v58999.
  rewrite ?node_58997.
  rewrite ?node_58998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
