(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes022.
Lemma node_23000 (s : N.State) (i : N.Inputs) :
  R.v23000 (state s) (inputs i) = Zmod.unsigned (N.v23000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23000 s i)) at 1.
  unfold R.v23000, N.v23000.
  rewrite ?node_8343.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23001 (s : N.State) (i : N.Inputs) :
  R.v23001 (state s) (inputs i) = Zmod.unsigned (N.v23001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23001 s i)) at 1.
  unfold R.v23001, N.v23001.
  unfold R.v6, N.v6.
  rewrite ?node_8467.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23002 (s : N.State) (i : N.Inputs) :
  R.v23002 (state s) (inputs i) = Zmod.unsigned (N.v23002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23002 s i)) at 1.
  unfold R.v23002, N.v23002.
  unfold R.v6, N.v6.
  rewrite ?node_8504.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23003 (s : N.State) (i : N.Inputs) :
  R.v23003 (state s) (inputs i) = Zmod.unsigned (N.v23003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23003 s i)) at 1.
  unfold R.v23003, N.v23003.
  rewrite ?node_23000.
  rewrite ?node_23001.
  rewrite ?node_23002.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23004 (s : N.State) (i : N.Inputs) :
  R.v23004 (state s) (inputs i) = Zmod.unsigned (N.v23004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23004 s i)) at 1.
  unfold R.v23004, N.v23004.
  rewrite ?node_22999.
  rewrite ?node_23003.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23005 (s : N.State) (i : N.Inputs) :
  R.v23005 (state s) (inputs i) = Zmod.unsigned (N.v23005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23005 s i)) at 1.
  unfold R.v23005, N.v23005.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23006 (s : N.State) (i : N.Inputs) :
  R.v23006 (state s) (inputs i) = Zmod.unsigned (N.v23006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23006 s i)) at 1.
  unfold R.v23006, N.v23006.
  unfold R.v16463, N.v16463.
  rewrite !state_r722_nr_5F722.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r722_nr_5F722 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23007 (s : N.State) (i : N.Inputs) :
  R.v23007 (state s) (inputs i) = Zmod.unsigned (N.v23007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23007 s i)) at 1.
  unfold R.v23007, N.v23007.
  unfold R.v6, N.v6.
  rewrite !state_r721_nr_5F721.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r721_nr_5F721 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23008 (s : N.State) (i : N.Inputs) :
  R.v23008 (state s) (inputs i) = Zmod.unsigned (N.v23008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23008 s i)) at 1.
  unfold R.v23008, N.v23008.
  unfold R.v6, N.v6.
  rewrite !state_r720_nr_5F720.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r720_nr_5F720 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23009 (s : N.State) (i : N.Inputs) :
  R.v23009 (state s) (inputs i) = Zmod.unsigned (N.v23009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23009 s i)) at 1.
  unfold R.v23009, N.v23009.
  rewrite ?node_23007.
  rewrite ?node_23008.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23010 (s : N.State) (i : N.Inputs) :
  R.v23010 (state s) (inputs i) = Zmod.unsigned (N.v23010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23010 s i)) at 1.
  unfold R.v23010, N.v23010.
  unfold R.v16484, N.v16484.
  rewrite ?node_23009.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23011 (s : N.State) (i : N.Inputs) :
  R.v23011 (state s) (inputs i) = Zmod.unsigned (N.v23011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23011 s i)) at 1.
  unfold R.v23011, N.v23011.
  rewrite ?node_23006.
  rewrite ?node_23010.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23012 (s : N.State) (i : N.Inputs) :
  R.v23012 (state s) (inputs i) = Zmod.unsigned (N.v23012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23012 s i)) at 1.
  unfold R.v23012, N.v23012.
  unfold R.v6, N.v6.
  rewrite ?node_23011.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23013 (s : N.State) (i : N.Inputs) :
  R.v23013 (state s) (inputs i) = Zmod.unsigned (N.v23013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23013 s i)) at 1.
  unfold R.v23013, N.v23013.
  rewrite ?node_8338.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23014 (s : N.State) (i : N.Inputs) :
  R.v23014 (state s) (inputs i) = Zmod.unsigned (N.v23014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23014 s i)) at 1.
  unfold R.v23014, N.v23014.
  unfold R.v6, N.v6.
  rewrite ?node_8467.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23015 (s : N.State) (i : N.Inputs) :
  R.v23015 (state s) (inputs i) = Zmod.unsigned (N.v23015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23015 s i)) at 1.
  unfold R.v23015, N.v23015.
  rewrite ?node_23013.
  rewrite ?node_23014.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23016 (s : N.State) (i : N.Inputs) :
  R.v23016 (state s) (inputs i) = Zmod.unsigned (N.v23016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23016 s i)) at 1.
  unfold R.v23016, N.v23016.
  rewrite ?node_23012.
  rewrite ?node_23015.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23017 (s : N.State) (i : N.Inputs) :
  R.v23017 (state s) (inputs i) = Zmod.unsigned (N.v23017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23017 s i)) at 1.
  unfold R.v23017, N.v23017.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23018 (s : N.State) (i : N.Inputs) :
  R.v23018 (state s) (inputs i) = Zmod.unsigned (N.v23018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23018 s i)) at 1.
  unfold R.v23018, N.v23018.
  rewrite ?node_8342.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23019 (s : N.State) (i : N.Inputs) :
  R.v23019 (state s) (inputs i) = Zmod.unsigned (N.v23019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23019 s i)) at 1.
  unfold R.v23019, N.v23019.
  unfold R.v6, N.v6.
  rewrite !state_r723_nr_5F723.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r723_nr_5F723 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23020 (s : N.State) (i : N.Inputs) :
  R.v23020 (state s) (inputs i) = Zmod.unsigned (N.v23020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23020 s i)) at 1.
  unfold R.v23020, N.v23020.
  unfold R.v6, N.v6.
  rewrite ?node_8338.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23021 (s : N.State) (i : N.Inputs) :
  R.v23021 (state s) (inputs i) = Zmod.unsigned (N.v23021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23021 s i)) at 1.
  unfold R.v23021, N.v23021.
  rewrite ?node_23019.
  rewrite ?node_23020.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23022 (s : N.State) (i : N.Inputs) :
  R.v23022 (state s) (inputs i) = Zmod.unsigned (N.v23022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23022 s i)) at 1.
  unfold R.v23022, N.v23022.
  unfold R.v16484, N.v16484.
  rewrite ?node_23021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23023 (s : N.State) (i : N.Inputs) :
  R.v23023 (state s) (inputs i) = Zmod.unsigned (N.v23023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23023 s i)) at 1.
  unfold R.v23023, N.v23023.
  rewrite ?node_23018.
  rewrite ?node_23022.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23024 (s : N.State) (i : N.Inputs) :
  R.v23024 (state s) (inputs i) = Zmod.unsigned (N.v23024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23024 s i)) at 1.
  unfold R.v23024, N.v23024.
  unfold R.v6, N.v6.
  rewrite ?node_23023.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23025 (s : N.State) (i : N.Inputs) :
  R.v23025 (state s) (inputs i) = Zmod.unsigned (N.v23025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23025 s i)) at 1.
  unfold R.v23025, N.v23025.
  rewrite ?node_8343.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23026 (s : N.State) (i : N.Inputs) :
  R.v23026 (state s) (inputs i) = Zmod.unsigned (N.v23026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23026 s i)) at 1.
  unfold R.v23026, N.v23026.
  unfold R.v6, N.v6.
  rewrite ?node_8504.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23027 (s : N.State) (i : N.Inputs) :
  R.v23027 (state s) (inputs i) = Zmod.unsigned (N.v23027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23027 s i)) at 1.
  unfold R.v23027, N.v23027.
  rewrite ?node_23025.
  rewrite ?node_23026.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23028 (s : N.State) (i : N.Inputs) :
  R.v23028 (state s) (inputs i) = Zmod.unsigned (N.v23028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23028 s i)) at 1.
  unfold R.v23028, N.v23028.
  rewrite ?node_23024.
  rewrite ?node_23027.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23029 (s : N.State) (i : N.Inputs) :
  R.v23029 (state s) (inputs i) = Zmod.unsigned (N.v23029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23029 s i)) at 1.
  unfold R.v23029, N.v23029.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23030 (s : N.State) (i : N.Inputs) :
  R.v23030 (state s) (inputs i) = Zmod.unsigned (N.v23030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23030 s i)) at 1.
  unfold R.v23030, N.v23030.
  unfold R.v16463, N.v16463.
  rewrite !state_r726_nr_5F726.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r726_nr_5F726 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23031 (s : N.State) (i : N.Inputs) :
  R.v23031 (state s) (inputs i) = Zmod.unsigned (N.v23031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23031 s i)) at 1.
  unfold R.v23031, N.v23031.
  unfold R.v6, N.v6.
  rewrite !state_r725_nr_5F725.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r725_nr_5F725 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23032 (s : N.State) (i : N.Inputs) :
  R.v23032 (state s) (inputs i) = Zmod.unsigned (N.v23032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23032 s i)) at 1.
  unfold R.v23032, N.v23032.
  unfold R.v6, N.v6.
  rewrite !state_r724_nr_5F724.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r724_nr_5F724 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23033 (s : N.State) (i : N.Inputs) :
  R.v23033 (state s) (inputs i) = Zmod.unsigned (N.v23033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23033 s i)) at 1.
  unfold R.v23033, N.v23033.
  rewrite ?node_23031.
  rewrite ?node_23032.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23034 (s : N.State) (i : N.Inputs) :
  R.v23034 (state s) (inputs i) = Zmod.unsigned (N.v23034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23034 s i)) at 1.
  unfold R.v23034, N.v23034.
  unfold R.v16484, N.v16484.
  rewrite ?node_23033.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23035 (s : N.State) (i : N.Inputs) :
  R.v23035 (state s) (inputs i) = Zmod.unsigned (N.v23035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23035 s i)) at 1.
  unfold R.v23035, N.v23035.
  rewrite ?node_23030.
  rewrite ?node_23034.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23036 (s : N.State) (i : N.Inputs) :
  R.v23036 (state s) (inputs i) = Zmod.unsigned (N.v23036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23036 s i)) at 1.
  unfold R.v23036, N.v23036.
  unfold R.v6, N.v6.
  rewrite ?node_23035.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23037 (s : N.State) (i : N.Inputs) :
  R.v23037 (state s) (inputs i) = Zmod.unsigned (N.v23037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23037 s i)) at 1.
  unfold R.v23037, N.v23037.
  rewrite ?node_8346.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23038 (s : N.State) (i : N.Inputs) :
  R.v23038 (state s) (inputs i) = Zmod.unsigned (N.v23038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23038 s i)) at 1.
  unfold R.v23038, N.v23038.
  unfold R.v6, N.v6.
  rewrite ?node_8507.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23039 (s : N.State) (i : N.Inputs) :
  R.v23039 (state s) (inputs i) = Zmod.unsigned (N.v23039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23039 s i)) at 1.
  unfold R.v23039, N.v23039.
  rewrite ?node_23037.
  rewrite ?node_23038.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23040 (s : N.State) (i : N.Inputs) :
  R.v23040 (state s) (inputs i) = Zmod.unsigned (N.v23040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23040 s i)) at 1.
  unfold R.v23040, N.v23040.
  rewrite ?node_23036.
  rewrite ?node_23039.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23041 (s : N.State) (i : N.Inputs) :
  R.v23041 (state s) (inputs i) = Zmod.unsigned (N.v23041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23041 s i)) at 1.
  unfold R.v23041, N.v23041.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23042 (s : N.State) (i : N.Inputs) :
  R.v23042 (state s) (inputs i) = Zmod.unsigned (N.v23042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23042 s i)) at 1.
  unfold R.v23042, N.v23042.
  rewrite ?node_8425.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23043 (s : N.State) (i : N.Inputs) :
  R.v23043 (state s) (inputs i) = Zmod.unsigned (N.v23043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23043 s i)) at 1.
  unfold R.v23043, N.v23043.
  unfold R.v16463, N.v16463.
  rewrite !state_r730_nr_5F730.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r730_nr_5F730 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23044 (s : N.State) (i : N.Inputs) :
  R.v23044 (state s) (inputs i) = Zmod.unsigned (N.v23044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23044 s i)) at 1.
  unfold R.v23044, N.v23044.
  unfold R.v16463, N.v16463.
  rewrite !state_r729_nr_5F729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r729_nr_5F729 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23045 (s : N.State) (i : N.Inputs) :
  R.v23045 (state s) (inputs i) = Zmod.unsigned (N.v23045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23045 s i)) at 1.
  unfold R.v23045, N.v23045.
  unfold R.v6, N.v6.
  rewrite !state_r728_nr_5F728.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r728_nr_5F728 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23046 (s : N.State) (i : N.Inputs) :
  R.v23046 (state s) (inputs i) = Zmod.unsigned (N.v23046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23046 s i)) at 1.
  unfold R.v23046, N.v23046.
  unfold R.v6, N.v6.
  rewrite !state_r727_nr_5F727.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r727_nr_5F727 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23047 (s : N.State) (i : N.Inputs) :
  R.v23047 (state s) (inputs i) = Zmod.unsigned (N.v23047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23047 s i)) at 1.
  unfold R.v23047, N.v23047.
  rewrite ?node_23045.
  rewrite ?node_23046.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23048 (s : N.State) (i : N.Inputs) :
  R.v23048 (state s) (inputs i) = Zmod.unsigned (N.v23048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23048 s i)) at 1.
  unfold R.v23048, N.v23048.
  unfold R.v16484, N.v16484.
  rewrite ?node_23047.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23049 (s : N.State) (i : N.Inputs) :
  R.v23049 (state s) (inputs i) = Zmod.unsigned (N.v23049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23049 s i)) at 1.
  unfold R.v23049, N.v23049.
  rewrite ?node_23042.
  rewrite ?node_23043.
  rewrite ?node_23044.
  rewrite ?node_23048.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23050 (s : N.State) (i : N.Inputs) :
  R.v23050 (state s) (inputs i) = Zmod.unsigned (N.v23050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23050 s i)) at 1.
  unfold R.v23050, N.v23050.
  unfold R.v6, N.v6.
  rewrite ?node_23049.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23051 (s : N.State) (i : N.Inputs) :
  R.v23051 (state s) (inputs i) = Zmod.unsigned (N.v23051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23051 s i)) at 1.
  unfold R.v23051, N.v23051.
  rewrite ?node_8426.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23052 (s : N.State) (i : N.Inputs) :
  R.v23052 (state s) (inputs i) = Zmod.unsigned (N.v23052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23052 s i)) at 1.
  unfold R.v23052, N.v23052.
  unfold R.v6, N.v6.
  rewrite ?node_8554.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23053 (s : N.State) (i : N.Inputs) :
  R.v23053 (state s) (inputs i) = Zmod.unsigned (N.v23053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23053 s i)) at 1.
  unfold R.v23053, N.v23053.
  unfold R.v6, N.v6.
  rewrite ?node_8605.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23054 (s : N.State) (i : N.Inputs) :
  R.v23054 (state s) (inputs i) = Zmod.unsigned (N.v23054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23054 s i)) at 1.
  unfold R.v23054, N.v23054.
  rewrite ?node_23051.
  rewrite ?node_23052.
  rewrite ?node_23053.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23055 (s : N.State) (i : N.Inputs) :
  R.v23055 (state s) (inputs i) = Zmod.unsigned (N.v23055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23055 s i)) at 1.
  unfold R.v23055, N.v23055.
  rewrite ?node_23050.
  rewrite ?node_23054.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23056 (s : N.State) (i : N.Inputs) :
  R.v23056 (state s) (inputs i) = Zmod.unsigned (N.v23056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23056 s i)) at 1.
  unfold R.v23056, N.v23056.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23057 (s : N.State) (i : N.Inputs) :
  R.v23057 (state s) (inputs i) = Zmod.unsigned (N.v23057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23057 s i)) at 1.
  unfold R.v23057, N.v23057.
  unfold R.v16463, N.v16463.
  rewrite !state_r729_nr_5F729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r729_nr_5F729 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23058 (s : N.State) (i : N.Inputs) :
  R.v23058 (state s) (inputs i) = Zmod.unsigned (N.v23058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23058 s i)) at 1.
  unfold R.v23058, N.v23058.
  unfold R.v6, N.v6.
  rewrite !state_r728_nr_5F728.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r728_nr_5F728 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23059 (s : N.State) (i : N.Inputs) :
  R.v23059 (state s) (inputs i) = Zmod.unsigned (N.v23059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23059 s i)) at 1.
  unfold R.v23059, N.v23059.
  unfold R.v6, N.v6.
  rewrite !state_r727_nr_5F727.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r727_nr_5F727 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23060 (s : N.State) (i : N.Inputs) :
  R.v23060 (state s) (inputs i) = Zmod.unsigned (N.v23060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23060 s i)) at 1.
  unfold R.v23060, N.v23060.
  rewrite ?node_23058.
  rewrite ?node_23059.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23061 (s : N.State) (i : N.Inputs) :
  R.v23061 (state s) (inputs i) = Zmod.unsigned (N.v23061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23061 s i)) at 1.
  unfold R.v23061, N.v23061.
  unfold R.v16484, N.v16484.
  rewrite ?node_23060.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23062 (s : N.State) (i : N.Inputs) :
  R.v23062 (state s) (inputs i) = Zmod.unsigned (N.v23062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23062 s i)) at 1.
  unfold R.v23062, N.v23062.
  rewrite ?node_23057.
  rewrite ?node_23061.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23063 (s : N.State) (i : N.Inputs) :
  R.v23063 (state s) (inputs i) = Zmod.unsigned (N.v23063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23063 s i)) at 1.
  unfold R.v23063, N.v23063.
  unfold R.v6, N.v6.
  rewrite ?node_23062.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23064 (s : N.State) (i : N.Inputs) :
  R.v23064 (state s) (inputs i) = Zmod.unsigned (N.v23064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23064 s i)) at 1.
  unfold R.v23064, N.v23064.
  rewrite ?node_8421.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23065 (s : N.State) (i : N.Inputs) :
  R.v23065 (state s) (inputs i) = Zmod.unsigned (N.v23065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23065 s i)) at 1.
  unfold R.v23065, N.v23065.
  unfold R.v6, N.v6.
  rewrite ?node_8554.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23066 (s : N.State) (i : N.Inputs) :
  R.v23066 (state s) (inputs i) = Zmod.unsigned (N.v23066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23066 s i)) at 1.
  unfold R.v23066, N.v23066.
  rewrite ?node_23064.
  rewrite ?node_23065.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23067 (s : N.State) (i : N.Inputs) :
  R.v23067 (state s) (inputs i) = Zmod.unsigned (N.v23067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23067 s i)) at 1.
  unfold R.v23067, N.v23067.
  rewrite ?node_23063.
  rewrite ?node_23066.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23068 (s : N.State) (i : N.Inputs) :
  R.v23068 (state s) (inputs i) = Zmod.unsigned (N.v23068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23068 s i)) at 1.
  unfold R.v23068, N.v23068.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23069 (s : N.State) (i : N.Inputs) :
  R.v23069 (state s) (inputs i) = Zmod.unsigned (N.v23069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23069 s i)) at 1.
  unfold R.v23069, N.v23069.
  rewrite ?node_8425.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23070 (s : N.State) (i : N.Inputs) :
  R.v23070 (state s) (inputs i) = Zmod.unsigned (N.v23070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23070 s i)) at 1.
  unfold R.v23070, N.v23070.
  unfold R.v6, N.v6.
  rewrite !state_r730_nr_5F730.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r730_nr_5F730 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23071 (s : N.State) (i : N.Inputs) :
  R.v23071 (state s) (inputs i) = Zmod.unsigned (N.v23071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23071 s i)) at 1.
  unfold R.v23071, N.v23071.
  unfold R.v6, N.v6.
  rewrite ?node_8421.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23072 (s : N.State) (i : N.Inputs) :
  R.v23072 (state s) (inputs i) = Zmod.unsigned (N.v23072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23072 s i)) at 1.
  unfold R.v23072, N.v23072.
  rewrite ?node_23070.
  rewrite ?node_23071.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23073 (s : N.State) (i : N.Inputs) :
  R.v23073 (state s) (inputs i) = Zmod.unsigned (N.v23073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23073 s i)) at 1.
  unfold R.v23073, N.v23073.
  unfold R.v16484, N.v16484.
  rewrite ?node_23072.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23074 (s : N.State) (i : N.Inputs) :
  R.v23074 (state s) (inputs i) = Zmod.unsigned (N.v23074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23074 s i)) at 1.
  unfold R.v23074, N.v23074.
  rewrite ?node_23069.
  rewrite ?node_23073.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23075 (s : N.State) (i : N.Inputs) :
  R.v23075 (state s) (inputs i) = Zmod.unsigned (N.v23075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23075 s i)) at 1.
  unfold R.v23075, N.v23075.
  unfold R.v6, N.v6.
  rewrite ?node_23074.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23076 (s : N.State) (i : N.Inputs) :
  R.v23076 (state s) (inputs i) = Zmod.unsigned (N.v23076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23076 s i)) at 1.
  unfold R.v23076, N.v23076.
  rewrite ?node_8426.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23077 (s : N.State) (i : N.Inputs) :
  R.v23077 (state s) (inputs i) = Zmod.unsigned (N.v23077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23077 s i)) at 1.
  unfold R.v23077, N.v23077.
  unfold R.v6, N.v6.
  rewrite ?node_8605.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23078 (s : N.State) (i : N.Inputs) :
  R.v23078 (state s) (inputs i) = Zmod.unsigned (N.v23078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23078 s i)) at 1.
  unfold R.v23078, N.v23078.
  rewrite ?node_23076.
  rewrite ?node_23077.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23079 (s : N.State) (i : N.Inputs) :
  R.v23079 (state s) (inputs i) = Zmod.unsigned (N.v23079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23079 s i)) at 1.
  unfold R.v23079, N.v23079.
  rewrite ?node_23075.
  rewrite ?node_23078.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23080 (s : N.State) (i : N.Inputs) :
  R.v23080 (state s) (inputs i) = Zmod.unsigned (N.v23080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23080 s i)) at 1.
  unfold R.v23080, N.v23080.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23081 (s : N.State) (i : N.Inputs) :
  R.v23081 (state s) (inputs i) = Zmod.unsigned (N.v23081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23081 s i)) at 1.
  unfold R.v23081, N.v23081.
  rewrite ?node_8432.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23082 (s : N.State) (i : N.Inputs) :
  R.v23082 (state s) (inputs i) = Zmod.unsigned (N.v23082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23082 s i)) at 1.
  unfold R.v23082, N.v23082.
  unfold R.v16463, N.v16463.
  rewrite !state_r734_nr_5F734.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r734_nr_5F734 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23083 (s : N.State) (i : N.Inputs) :
  R.v23083 (state s) (inputs i) = Zmod.unsigned (N.v23083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23083 s i)) at 1.
  unfold R.v23083, N.v23083.
  unfold R.v16463, N.v16463.
  rewrite !state_r733_nr_5F733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r733_nr_5F733 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23084 (s : N.State) (i : N.Inputs) :
  R.v23084 (state s) (inputs i) = Zmod.unsigned (N.v23084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23084 s i)) at 1.
  unfold R.v23084, N.v23084.
  unfold R.v6, N.v6.
  rewrite !state_r732_nr_5F732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r732_nr_5F732 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23085 (s : N.State) (i : N.Inputs) :
  R.v23085 (state s) (inputs i) = Zmod.unsigned (N.v23085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23085 s i)) at 1.
  unfold R.v23085, N.v23085.
  unfold R.v6, N.v6.
  rewrite !state_r731_nr_5F731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r731_nr_5F731 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23086 (s : N.State) (i : N.Inputs) :
  R.v23086 (state s) (inputs i) = Zmod.unsigned (N.v23086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23086 s i)) at 1.
  unfold R.v23086, N.v23086.
  rewrite ?node_23084.
  rewrite ?node_23085.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23087 (s : N.State) (i : N.Inputs) :
  R.v23087 (state s) (inputs i) = Zmod.unsigned (N.v23087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23087 s i)) at 1.
  unfold R.v23087, N.v23087.
  unfold R.v16484, N.v16484.
  rewrite ?node_23086.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23088 (s : N.State) (i : N.Inputs) :
  R.v23088 (state s) (inputs i) = Zmod.unsigned (N.v23088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23088 s i)) at 1.
  unfold R.v23088, N.v23088.
  rewrite ?node_23081.
  rewrite ?node_23082.
  rewrite ?node_23083.
  rewrite ?node_23087.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23089 (s : N.State) (i : N.Inputs) :
  R.v23089 (state s) (inputs i) = Zmod.unsigned (N.v23089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23089 s i)) at 1.
  unfold R.v23089, N.v23089.
  unfold R.v6, N.v6.
  rewrite ?node_23088.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23090 (s : N.State) (i : N.Inputs) :
  R.v23090 (state s) (inputs i) = Zmod.unsigned (N.v23090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23090 s i)) at 1.
  unfold R.v23090, N.v23090.
  rewrite ?node_8433.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23091 (s : N.State) (i : N.Inputs) :
  R.v23091 (state s) (inputs i) = Zmod.unsigned (N.v23091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23091 s i)) at 1.
  unfold R.v23091, N.v23091.
  unfold R.v6, N.v6.
  rewrite ?node_8561.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23092 (s : N.State) (i : N.Inputs) :
  R.v23092 (state s) (inputs i) = Zmod.unsigned (N.v23092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23092 s i)) at 1.
  unfold R.v23092, N.v23092.
  unfold R.v6, N.v6.
  rewrite ?node_8614.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23093 (s : N.State) (i : N.Inputs) :
  R.v23093 (state s) (inputs i) = Zmod.unsigned (N.v23093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23093 s i)) at 1.
  unfold R.v23093, N.v23093.
  rewrite ?node_23090.
  rewrite ?node_23091.
  rewrite ?node_23092.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23094 (s : N.State) (i : N.Inputs) :
  R.v23094 (state s) (inputs i) = Zmod.unsigned (N.v23094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23094 s i)) at 1.
  unfold R.v23094, N.v23094.
  rewrite ?node_23089.
  rewrite ?node_23093.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23095 (s : N.State) (i : N.Inputs) :
  R.v23095 (state s) (inputs i) = Zmod.unsigned (N.v23095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23095 s i)) at 1.
  unfold R.v23095, N.v23095.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23096 (s : N.State) (i : N.Inputs) :
  R.v23096 (state s) (inputs i) = Zmod.unsigned (N.v23096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23096 s i)) at 1.
  unfold R.v23096, N.v23096.
  unfold R.v16463, N.v16463.
  rewrite !state_r733_nr_5F733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r733_nr_5F733 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23097 (s : N.State) (i : N.Inputs) :
  R.v23097 (state s) (inputs i) = Zmod.unsigned (N.v23097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23097 s i)) at 1.
  unfold R.v23097, N.v23097.
  unfold R.v6, N.v6.
  rewrite !state_r732_nr_5F732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r732_nr_5F732 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23098 (s : N.State) (i : N.Inputs) :
  R.v23098 (state s) (inputs i) = Zmod.unsigned (N.v23098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23098 s i)) at 1.
  unfold R.v23098, N.v23098.
  unfold R.v6, N.v6.
  rewrite !state_r731_nr_5F731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r731_nr_5F731 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23099 (s : N.State) (i : N.Inputs) :
  R.v23099 (state s) (inputs i) = Zmod.unsigned (N.v23099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23099 s i)) at 1.
  unfold R.v23099, N.v23099.
  rewrite ?node_23097.
  rewrite ?node_23098.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23100 (s : N.State) (i : N.Inputs) :
  R.v23100 (state s) (inputs i) = Zmod.unsigned (N.v23100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23100 s i)) at 1.
  unfold R.v23100, N.v23100.
  unfold R.v16484, N.v16484.
  rewrite ?node_23099.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23101 (s : N.State) (i : N.Inputs) :
  R.v23101 (state s) (inputs i) = Zmod.unsigned (N.v23101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23101 s i)) at 1.
  unfold R.v23101, N.v23101.
  rewrite ?node_23096.
  rewrite ?node_23100.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23102 (s : N.State) (i : N.Inputs) :
  R.v23102 (state s) (inputs i) = Zmod.unsigned (N.v23102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23102 s i)) at 1.
  unfold R.v23102, N.v23102.
  unfold R.v6, N.v6.
  rewrite ?node_23101.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23103 (s : N.State) (i : N.Inputs) :
  R.v23103 (state s) (inputs i) = Zmod.unsigned (N.v23103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23103 s i)) at 1.
  unfold R.v23103, N.v23103.
  rewrite ?node_8428.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23104 (s : N.State) (i : N.Inputs) :
  R.v23104 (state s) (inputs i) = Zmod.unsigned (N.v23104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23104 s i)) at 1.
  unfold R.v23104, N.v23104.
  unfold R.v6, N.v6.
  rewrite ?node_8561.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23105 (s : N.State) (i : N.Inputs) :
  R.v23105 (state s) (inputs i) = Zmod.unsigned (N.v23105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23105 s i)) at 1.
  unfold R.v23105, N.v23105.
  rewrite ?node_23103.
  rewrite ?node_23104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23106 (s : N.State) (i : N.Inputs) :
  R.v23106 (state s) (inputs i) = Zmod.unsigned (N.v23106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23106 s i)) at 1.
  unfold R.v23106, N.v23106.
  rewrite ?node_23102.
  rewrite ?node_23105.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23107 (s : N.State) (i : N.Inputs) :
  R.v23107 (state s) (inputs i) = Zmod.unsigned (N.v23107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23107 s i)) at 1.
  unfold R.v23107, N.v23107.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23108 (s : N.State) (i : N.Inputs) :
  R.v23108 (state s) (inputs i) = Zmod.unsigned (N.v23108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23108 s i)) at 1.
  unfold R.v23108, N.v23108.
  rewrite ?node_8432.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23109 (s : N.State) (i : N.Inputs) :
  R.v23109 (state s) (inputs i) = Zmod.unsigned (N.v23109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23109 s i)) at 1.
  unfold R.v23109, N.v23109.
  unfold R.v6, N.v6.
  rewrite !state_r734_nr_5F734.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r734_nr_5F734 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23110 (s : N.State) (i : N.Inputs) :
  R.v23110 (state s) (inputs i) = Zmod.unsigned (N.v23110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23110 s i)) at 1.
  unfold R.v23110, N.v23110.
  unfold R.v6, N.v6.
  rewrite ?node_8428.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23111 (s : N.State) (i : N.Inputs) :
  R.v23111 (state s) (inputs i) = Zmod.unsigned (N.v23111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23111 s i)) at 1.
  unfold R.v23111, N.v23111.
  rewrite ?node_23109.
  rewrite ?node_23110.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23112 (s : N.State) (i : N.Inputs) :
  R.v23112 (state s) (inputs i) = Zmod.unsigned (N.v23112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23112 s i)) at 1.
  unfold R.v23112, N.v23112.
  unfold R.v16484, N.v16484.
  rewrite ?node_23111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23113 (s : N.State) (i : N.Inputs) :
  R.v23113 (state s) (inputs i) = Zmod.unsigned (N.v23113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23113 s i)) at 1.
  unfold R.v23113, N.v23113.
  rewrite ?node_23108.
  rewrite ?node_23112.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23114 (s : N.State) (i : N.Inputs) :
  R.v23114 (state s) (inputs i) = Zmod.unsigned (N.v23114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23114 s i)) at 1.
  unfold R.v23114, N.v23114.
  unfold R.v6, N.v6.
  rewrite ?node_23113.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23115 (s : N.State) (i : N.Inputs) :
  R.v23115 (state s) (inputs i) = Zmod.unsigned (N.v23115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23115 s i)) at 1.
  unfold R.v23115, N.v23115.
  rewrite ?node_8433.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23116 (s : N.State) (i : N.Inputs) :
  R.v23116 (state s) (inputs i) = Zmod.unsigned (N.v23116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23116 s i)) at 1.
  unfold R.v23116, N.v23116.
  unfold R.v6, N.v6.
  rewrite ?node_8614.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23117 (s : N.State) (i : N.Inputs) :
  R.v23117 (state s) (inputs i) = Zmod.unsigned (N.v23117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23117 s i)) at 1.
  unfold R.v23117, N.v23117.
  rewrite ?node_23115.
  rewrite ?node_23116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23118 (s : N.State) (i : N.Inputs) :
  R.v23118 (state s) (inputs i) = Zmod.unsigned (N.v23118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23118 s i)) at 1.
  unfold R.v23118, N.v23118.
  rewrite ?node_23114.
  rewrite ?node_23117.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23119 (s : N.State) (i : N.Inputs) :
  R.v23119 (state s) (inputs i) = Zmod.unsigned (N.v23119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23119 s i)) at 1.
  unfold R.v23119, N.v23119.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23120 (s : N.State) (i : N.Inputs) :
  R.v23120 (state s) (inputs i) = Zmod.unsigned (N.v23120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23120 s i)) at 1.
  unfold R.v23120, N.v23120.
  rewrite ?node_8440.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23121 (s : N.State) (i : N.Inputs) :
  R.v23121 (state s) (inputs i) = Zmod.unsigned (N.v23121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23121 s i)) at 1.
  unfold R.v23121, N.v23121.
  unfold R.v16463, N.v16463.
  rewrite !state_r738_nr_5F738.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r738_nr_5F738 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23122 (s : N.State) (i : N.Inputs) :
  R.v23122 (state s) (inputs i) = Zmod.unsigned (N.v23122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23122 s i)) at 1.
  unfold R.v23122, N.v23122.
  unfold R.v16463, N.v16463.
  rewrite !state_r737_nr_5F737.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r737_nr_5F737 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23123 (s : N.State) (i : N.Inputs) :
  R.v23123 (state s) (inputs i) = Zmod.unsigned (N.v23123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23123 s i)) at 1.
  unfold R.v23123, N.v23123.
  unfold R.v6, N.v6.
  rewrite !state_r736_nr_5F736.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r736_nr_5F736 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23124 (s : N.State) (i : N.Inputs) :
  R.v23124 (state s) (inputs i) = Zmod.unsigned (N.v23124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23124 s i)) at 1.
  unfold R.v23124, N.v23124.
  unfold R.v6, N.v6.
  rewrite !state_r735_nr_5F735.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r735_nr_5F735 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23125 (s : N.State) (i : N.Inputs) :
  R.v23125 (state s) (inputs i) = Zmod.unsigned (N.v23125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23125 s i)) at 1.
  unfold R.v23125, N.v23125.
  rewrite ?node_23123.
  rewrite ?node_23124.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23126 (s : N.State) (i : N.Inputs) :
  R.v23126 (state s) (inputs i) = Zmod.unsigned (N.v23126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23126 s i)) at 1.
  unfold R.v23126, N.v23126.
  unfold R.v16484, N.v16484.
  rewrite ?node_23125.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23127 (s : N.State) (i : N.Inputs) :
  R.v23127 (state s) (inputs i) = Zmod.unsigned (N.v23127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23127 s i)) at 1.
  unfold R.v23127, N.v23127.
  rewrite ?node_23120.
  rewrite ?node_23121.
  rewrite ?node_23122.
  rewrite ?node_23126.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23128 (s : N.State) (i : N.Inputs) :
  R.v23128 (state s) (inputs i) = Zmod.unsigned (N.v23128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23128 s i)) at 1.
  unfold R.v23128, N.v23128.
  unfold R.v6, N.v6.
  rewrite ?node_23127.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23129 (s : N.State) (i : N.Inputs) :
  R.v23129 (state s) (inputs i) = Zmod.unsigned (N.v23129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23129 s i)) at 1.
  unfold R.v23129, N.v23129.
  rewrite ?node_8441.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23130 (s : N.State) (i : N.Inputs) :
  R.v23130 (state s) (inputs i) = Zmod.unsigned (N.v23130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23130 s i)) at 1.
  unfold R.v23130, N.v23130.
  unfold R.v6, N.v6.
  rewrite ?node_8569.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23131 (s : N.State) (i : N.Inputs) :
  R.v23131 (state s) (inputs i) = Zmod.unsigned (N.v23131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23131 s i)) at 1.
  unfold R.v23131, N.v23131.
  unfold R.v6, N.v6.
  rewrite ?node_8617.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23132 (s : N.State) (i : N.Inputs) :
  R.v23132 (state s) (inputs i) = Zmod.unsigned (N.v23132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23132 s i)) at 1.
  unfold R.v23132, N.v23132.
  rewrite ?node_23129.
  rewrite ?node_23130.
  rewrite ?node_23131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23133 (s : N.State) (i : N.Inputs) :
  R.v23133 (state s) (inputs i) = Zmod.unsigned (N.v23133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23133 s i)) at 1.
  unfold R.v23133, N.v23133.
  rewrite ?node_23128.
  rewrite ?node_23132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23134 (s : N.State) (i : N.Inputs) :
  R.v23134 (state s) (inputs i) = Zmod.unsigned (N.v23134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23134 s i)) at 1.
  unfold R.v23134, N.v23134.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23135 (s : N.State) (i : N.Inputs) :
  R.v23135 (state s) (inputs i) = Zmod.unsigned (N.v23135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23135 s i)) at 1.
  unfold R.v23135, N.v23135.
  unfold R.v16463, N.v16463.
  rewrite !state_r737_nr_5F737.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r737_nr_5F737 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23136 (s : N.State) (i : N.Inputs) :
  R.v23136 (state s) (inputs i) = Zmod.unsigned (N.v23136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23136 s i)) at 1.
  unfold R.v23136, N.v23136.
  unfold R.v6, N.v6.
  rewrite !state_r736_nr_5F736.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r736_nr_5F736 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23137 (s : N.State) (i : N.Inputs) :
  R.v23137 (state s) (inputs i) = Zmod.unsigned (N.v23137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23137 s i)) at 1.
  unfold R.v23137, N.v23137.
  unfold R.v6, N.v6.
  rewrite !state_r735_nr_5F735.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r735_nr_5F735 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23138 (s : N.State) (i : N.Inputs) :
  R.v23138 (state s) (inputs i) = Zmod.unsigned (N.v23138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23138 s i)) at 1.
  unfold R.v23138, N.v23138.
  rewrite ?node_23136.
  rewrite ?node_23137.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23139 (s : N.State) (i : N.Inputs) :
  R.v23139 (state s) (inputs i) = Zmod.unsigned (N.v23139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23139 s i)) at 1.
  unfold R.v23139, N.v23139.
  unfold R.v16484, N.v16484.
  rewrite ?node_23138.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23140 (s : N.State) (i : N.Inputs) :
  R.v23140 (state s) (inputs i) = Zmod.unsigned (N.v23140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23140 s i)) at 1.
  unfold R.v23140, N.v23140.
  rewrite ?node_23135.
  rewrite ?node_23139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23141 (s : N.State) (i : N.Inputs) :
  R.v23141 (state s) (inputs i) = Zmod.unsigned (N.v23141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23141 s i)) at 1.
  unfold R.v23141, N.v23141.
  unfold R.v6, N.v6.
  rewrite ?node_23140.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23142 (s : N.State) (i : N.Inputs) :
  R.v23142 (state s) (inputs i) = Zmod.unsigned (N.v23142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23142 s i)) at 1.
  unfold R.v23142, N.v23142.
  rewrite ?node_8436.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23143 (s : N.State) (i : N.Inputs) :
  R.v23143 (state s) (inputs i) = Zmod.unsigned (N.v23143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23143 s i)) at 1.
  unfold R.v23143, N.v23143.
  unfold R.v6, N.v6.
  rewrite ?node_8569.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23144 (s : N.State) (i : N.Inputs) :
  R.v23144 (state s) (inputs i) = Zmod.unsigned (N.v23144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23144 s i)) at 1.
  unfold R.v23144, N.v23144.
  rewrite ?node_23142.
  rewrite ?node_23143.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23145 (s : N.State) (i : N.Inputs) :
  R.v23145 (state s) (inputs i) = Zmod.unsigned (N.v23145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23145 s i)) at 1.
  unfold R.v23145, N.v23145.
  rewrite ?node_23141.
  rewrite ?node_23144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23146 (s : N.State) (i : N.Inputs) :
  R.v23146 (state s) (inputs i) = Zmod.unsigned (N.v23146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23146 s i)) at 1.
  unfold R.v23146, N.v23146.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23147 (s : N.State) (i : N.Inputs) :
  R.v23147 (state s) (inputs i) = Zmod.unsigned (N.v23147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23147 s i)) at 1.
  unfold R.v23147, N.v23147.
  rewrite ?node_8440.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23148 (s : N.State) (i : N.Inputs) :
  R.v23148 (state s) (inputs i) = Zmod.unsigned (N.v23148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23148 s i)) at 1.
  unfold R.v23148, N.v23148.
  unfold R.v6, N.v6.
  rewrite !state_r738_nr_5F738.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r738_nr_5F738 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23149 (s : N.State) (i : N.Inputs) :
  R.v23149 (state s) (inputs i) = Zmod.unsigned (N.v23149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23149 s i)) at 1.
  unfold R.v23149, N.v23149.
  unfold R.v6, N.v6.
  rewrite ?node_8436.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23150 (s : N.State) (i : N.Inputs) :
  R.v23150 (state s) (inputs i) = Zmod.unsigned (N.v23150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23150 s i)) at 1.
  unfold R.v23150, N.v23150.
  rewrite ?node_23148.
  rewrite ?node_23149.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23151 (s : N.State) (i : N.Inputs) :
  R.v23151 (state s) (inputs i) = Zmod.unsigned (N.v23151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23151 s i)) at 1.
  unfold R.v23151, N.v23151.
  unfold R.v16484, N.v16484.
  rewrite ?node_23150.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23152 (s : N.State) (i : N.Inputs) :
  R.v23152 (state s) (inputs i) = Zmod.unsigned (N.v23152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23152 s i)) at 1.
  unfold R.v23152, N.v23152.
  rewrite ?node_23147.
  rewrite ?node_23151.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23153 (s : N.State) (i : N.Inputs) :
  R.v23153 (state s) (inputs i) = Zmod.unsigned (N.v23153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23153 s i)) at 1.
  unfold R.v23153, N.v23153.
  unfold R.v6, N.v6.
  rewrite ?node_23152.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23154 (s : N.State) (i : N.Inputs) :
  R.v23154 (state s) (inputs i) = Zmod.unsigned (N.v23154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23154 s i)) at 1.
  unfold R.v23154, N.v23154.
  rewrite ?node_8441.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23155 (s : N.State) (i : N.Inputs) :
  R.v23155 (state s) (inputs i) = Zmod.unsigned (N.v23155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23155 s i)) at 1.
  unfold R.v23155, N.v23155.
  unfold R.v6, N.v6.
  rewrite ?node_8617.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23156 (s : N.State) (i : N.Inputs) :
  R.v23156 (state s) (inputs i) = Zmod.unsigned (N.v23156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23156 s i)) at 1.
  unfold R.v23156, N.v23156.
  rewrite ?node_23154.
  rewrite ?node_23155.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23157 (s : N.State) (i : N.Inputs) :
  R.v23157 (state s) (inputs i) = Zmod.unsigned (N.v23157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23157 s i)) at 1.
  unfold R.v23157, N.v23157.
  rewrite ?node_23153.
  rewrite ?node_23156.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23158 (s : N.State) (i : N.Inputs) :
  R.v23158 (state s) (inputs i) = Zmod.unsigned (N.v23158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23158 s i)) at 1.
  unfold R.v23158, N.v23158.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23159 (s : N.State) (i : N.Inputs) :
  R.v23159 (state s) (inputs i) = Zmod.unsigned (N.v23159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23159 s i)) at 1.
  unfold R.v23159, N.v23159.
  rewrite ?node_8448.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23160 (s : N.State) (i : N.Inputs) :
  R.v23160 (state s) (inputs i) = Zmod.unsigned (N.v23160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23160 s i)) at 1.
  unfold R.v23160, N.v23160.
  unfold R.v16463, N.v16463.
  rewrite !state_r742_nr_5F742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r742_nr_5F742 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23161 (s : N.State) (i : N.Inputs) :
  R.v23161 (state s) (inputs i) = Zmod.unsigned (N.v23161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23161 s i)) at 1.
  unfold R.v23161, N.v23161.
  unfold R.v16463, N.v16463.
  rewrite !state_r741_nr_5F741.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r741_nr_5F741 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23162 (s : N.State) (i : N.Inputs) :
  R.v23162 (state s) (inputs i) = Zmod.unsigned (N.v23162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23162 s i)) at 1.
  unfold R.v23162, N.v23162.
  unfold R.v6, N.v6.
  rewrite !state_r740_nr_5F740.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r740_nr_5F740 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23163 (s : N.State) (i : N.Inputs) :
  R.v23163 (state s) (inputs i) = Zmod.unsigned (N.v23163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23163 s i)) at 1.
  unfold R.v23163, N.v23163.
  unfold R.v6, N.v6.
  rewrite !state_r739_nr_5F739.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r739_nr_5F739 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23164 (s : N.State) (i : N.Inputs) :
  R.v23164 (state s) (inputs i) = Zmod.unsigned (N.v23164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23164 s i)) at 1.
  unfold R.v23164, N.v23164.
  rewrite ?node_23162.
  rewrite ?node_23163.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23165 (s : N.State) (i : N.Inputs) :
  R.v23165 (state s) (inputs i) = Zmod.unsigned (N.v23165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23165 s i)) at 1.
  unfold R.v23165, N.v23165.
  unfold R.v16484, N.v16484.
  rewrite ?node_23164.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23166 (s : N.State) (i : N.Inputs) :
  R.v23166 (state s) (inputs i) = Zmod.unsigned (N.v23166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23166 s i)) at 1.
  unfold R.v23166, N.v23166.
  rewrite ?node_23159.
  rewrite ?node_23160.
  rewrite ?node_23161.
  rewrite ?node_23165.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23167 (s : N.State) (i : N.Inputs) :
  R.v23167 (state s) (inputs i) = Zmod.unsigned (N.v23167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23167 s i)) at 1.
  unfold R.v23167, N.v23167.
  unfold R.v6, N.v6.
  rewrite ?node_23166.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23168 (s : N.State) (i : N.Inputs) :
  R.v23168 (state s) (inputs i) = Zmod.unsigned (N.v23168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23168 s i)) at 1.
  unfold R.v23168, N.v23168.
  rewrite ?node_8449.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23169 (s : N.State) (i : N.Inputs) :
  R.v23169 (state s) (inputs i) = Zmod.unsigned (N.v23169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23169 s i)) at 1.
  unfold R.v23169, N.v23169.
  unfold R.v6, N.v6.
  rewrite ?node_8577.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23170 (s : N.State) (i : N.Inputs) :
  R.v23170 (state s) (inputs i) = Zmod.unsigned (N.v23170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23170 s i)) at 1.
  unfold R.v23170, N.v23170.
  unfold R.v6, N.v6.
  rewrite ?node_8621.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23171 (s : N.State) (i : N.Inputs) :
  R.v23171 (state s) (inputs i) = Zmod.unsigned (N.v23171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23171 s i)) at 1.
  unfold R.v23171, N.v23171.
  rewrite ?node_23168.
  rewrite ?node_23169.
  rewrite ?node_23170.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23172 (s : N.State) (i : N.Inputs) :
  R.v23172 (state s) (inputs i) = Zmod.unsigned (N.v23172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23172 s i)) at 1.
  unfold R.v23172, N.v23172.
  rewrite ?node_23167.
  rewrite ?node_23171.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23173 (s : N.State) (i : N.Inputs) :
  R.v23173 (state s) (inputs i) = Zmod.unsigned (N.v23173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23173 s i)) at 1.
  unfold R.v23173, N.v23173.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23174 (s : N.State) (i : N.Inputs) :
  R.v23174 (state s) (inputs i) = Zmod.unsigned (N.v23174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23174 s i)) at 1.
  unfold R.v23174, N.v23174.
  unfold R.v16463, N.v16463.
  rewrite !state_r741_nr_5F741.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r741_nr_5F741 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23175 (s : N.State) (i : N.Inputs) :
  R.v23175 (state s) (inputs i) = Zmod.unsigned (N.v23175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23175 s i)) at 1.
  unfold R.v23175, N.v23175.
  unfold R.v6, N.v6.
  rewrite !state_r740_nr_5F740.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r740_nr_5F740 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23176 (s : N.State) (i : N.Inputs) :
  R.v23176 (state s) (inputs i) = Zmod.unsigned (N.v23176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23176 s i)) at 1.
  unfold R.v23176, N.v23176.
  unfold R.v6, N.v6.
  rewrite !state_r739_nr_5F739.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r739_nr_5F739 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23177 (s : N.State) (i : N.Inputs) :
  R.v23177 (state s) (inputs i) = Zmod.unsigned (N.v23177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23177 s i)) at 1.
  unfold R.v23177, N.v23177.
  rewrite ?node_23175.
  rewrite ?node_23176.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23178 (s : N.State) (i : N.Inputs) :
  R.v23178 (state s) (inputs i) = Zmod.unsigned (N.v23178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23178 s i)) at 1.
  unfold R.v23178, N.v23178.
  unfold R.v16484, N.v16484.
  rewrite ?node_23177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23179 (s : N.State) (i : N.Inputs) :
  R.v23179 (state s) (inputs i) = Zmod.unsigned (N.v23179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23179 s i)) at 1.
  unfold R.v23179, N.v23179.
  rewrite ?node_23174.
  rewrite ?node_23178.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23180 (s : N.State) (i : N.Inputs) :
  R.v23180 (state s) (inputs i) = Zmod.unsigned (N.v23180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23180 s i)) at 1.
  unfold R.v23180, N.v23180.
  unfold R.v6, N.v6.
  rewrite ?node_23179.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23181 (s : N.State) (i : N.Inputs) :
  R.v23181 (state s) (inputs i) = Zmod.unsigned (N.v23181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23181 s i)) at 1.
  unfold R.v23181, N.v23181.
  rewrite ?node_8444.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23182 (s : N.State) (i : N.Inputs) :
  R.v23182 (state s) (inputs i) = Zmod.unsigned (N.v23182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23182 s i)) at 1.
  unfold R.v23182, N.v23182.
  unfold R.v6, N.v6.
  rewrite ?node_8577.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23183 (s : N.State) (i : N.Inputs) :
  R.v23183 (state s) (inputs i) = Zmod.unsigned (N.v23183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23183 s i)) at 1.
  unfold R.v23183, N.v23183.
  rewrite ?node_23181.
  rewrite ?node_23182.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23184 (s : N.State) (i : N.Inputs) :
  R.v23184 (state s) (inputs i) = Zmod.unsigned (N.v23184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23184 s i)) at 1.
  unfold R.v23184, N.v23184.
  rewrite ?node_23180.
  rewrite ?node_23183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23185 (s : N.State) (i : N.Inputs) :
  R.v23185 (state s) (inputs i) = Zmod.unsigned (N.v23185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23185 s i)) at 1.
  unfold R.v23185, N.v23185.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23186 (s : N.State) (i : N.Inputs) :
  R.v23186 (state s) (inputs i) = Zmod.unsigned (N.v23186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23186 s i)) at 1.
  unfold R.v23186, N.v23186.
  rewrite ?node_8448.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23187 (s : N.State) (i : N.Inputs) :
  R.v23187 (state s) (inputs i) = Zmod.unsigned (N.v23187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23187 s i)) at 1.
  unfold R.v23187, N.v23187.
  unfold R.v6, N.v6.
  rewrite !state_r742_nr_5F742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r742_nr_5F742 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23188 (s : N.State) (i : N.Inputs) :
  R.v23188 (state s) (inputs i) = Zmod.unsigned (N.v23188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23188 s i)) at 1.
  unfold R.v23188, N.v23188.
  unfold R.v6, N.v6.
  rewrite ?node_8444.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23189 (s : N.State) (i : N.Inputs) :
  R.v23189 (state s) (inputs i) = Zmod.unsigned (N.v23189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23189 s i)) at 1.
  unfold R.v23189, N.v23189.
  rewrite ?node_23187.
  rewrite ?node_23188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23190 (s : N.State) (i : N.Inputs) :
  R.v23190 (state s) (inputs i) = Zmod.unsigned (N.v23190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23190 s i)) at 1.
  unfold R.v23190, N.v23190.
  unfold R.v16484, N.v16484.
  rewrite ?node_23189.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23191 (s : N.State) (i : N.Inputs) :
  R.v23191 (state s) (inputs i) = Zmod.unsigned (N.v23191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23191 s i)) at 1.
  unfold R.v23191, N.v23191.
  rewrite ?node_23186.
  rewrite ?node_23190.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23192 (s : N.State) (i : N.Inputs) :
  R.v23192 (state s) (inputs i) = Zmod.unsigned (N.v23192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23192 s i)) at 1.
  unfold R.v23192, N.v23192.
  unfold R.v6, N.v6.
  rewrite ?node_23191.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23193 (s : N.State) (i : N.Inputs) :
  R.v23193 (state s) (inputs i) = Zmod.unsigned (N.v23193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23193 s i)) at 1.
  unfold R.v23193, N.v23193.
  rewrite ?node_8449.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23194 (s : N.State) (i : N.Inputs) :
  R.v23194 (state s) (inputs i) = Zmod.unsigned (N.v23194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23194 s i)) at 1.
  unfold R.v23194, N.v23194.
  unfold R.v6, N.v6.
  rewrite ?node_8621.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23195 (s : N.State) (i : N.Inputs) :
  R.v23195 (state s) (inputs i) = Zmod.unsigned (N.v23195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23195 s i)) at 1.
  unfold R.v23195, N.v23195.
  rewrite ?node_23193.
  rewrite ?node_23194.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23196 (s : N.State) (i : N.Inputs) :
  R.v23196 (state s) (inputs i) = Zmod.unsigned (N.v23196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23196 s i)) at 1.
  unfold R.v23196, N.v23196.
  rewrite ?node_23192.
  rewrite ?node_23195.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23197 (s : N.State) (i : N.Inputs) :
  R.v23197 (state s) (inputs i) = Zmod.unsigned (N.v23197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23197 s i)) at 1.
  unfold R.v23197, N.v23197.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23198 (s : N.State) (i : N.Inputs) :
  R.v23198 (state s) (inputs i) = Zmod.unsigned (N.v23198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23198 s i)) at 1.
  unfold R.v23198, N.v23198.
  rewrite ?node_8460.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23199 (s : N.State) (i : N.Inputs) :
  R.v23199 (state s) (inputs i) = Zmod.unsigned (N.v23199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23199 s i)) at 1.
  unfold R.v23199, N.v23199.
  unfold R.v16463, N.v16463.
  rewrite !state_r746_nr_5F746.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r746_nr_5F746 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23200 (s : N.State) (i : N.Inputs) :
  R.v23200 (state s) (inputs i) = Zmod.unsigned (N.v23200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23200 s i)) at 1.
  unfold R.v23200, N.v23200.
  unfold R.v16463, N.v16463.
  rewrite !state_r745_nr_5F745.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r745_nr_5F745 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23201 (s : N.State) (i : N.Inputs) :
  R.v23201 (state s) (inputs i) = Zmod.unsigned (N.v23201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23201 s i)) at 1.
  unfold R.v23201, N.v23201.
  unfold R.v6, N.v6.
  rewrite !state_r744_nr_5F744.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r744_nr_5F744 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23202 (s : N.State) (i : N.Inputs) :
  R.v23202 (state s) (inputs i) = Zmod.unsigned (N.v23202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23202 s i)) at 1.
  unfold R.v23202, N.v23202.
  unfold R.v6, N.v6.
  rewrite !state_r743_nr_5F743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r743_nr_5F743 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23203 (s : N.State) (i : N.Inputs) :
  R.v23203 (state s) (inputs i) = Zmod.unsigned (N.v23203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23203 s i)) at 1.
  unfold R.v23203, N.v23203.
  rewrite ?node_23201.
  rewrite ?node_23202.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23204 (s : N.State) (i : N.Inputs) :
  R.v23204 (state s) (inputs i) = Zmod.unsigned (N.v23204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23204 s i)) at 1.
  unfold R.v23204, N.v23204.
  unfold R.v16484, N.v16484.
  rewrite ?node_23203.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23205 (s : N.State) (i : N.Inputs) :
  R.v23205 (state s) (inputs i) = Zmod.unsigned (N.v23205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23205 s i)) at 1.
  unfold R.v23205, N.v23205.
  rewrite ?node_23198.
  rewrite ?node_23199.
  rewrite ?node_23200.
  rewrite ?node_23204.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23206 (s : N.State) (i : N.Inputs) :
  R.v23206 (state s) (inputs i) = Zmod.unsigned (N.v23206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23206 s i)) at 1.
  unfold R.v23206, N.v23206.
  unfold R.v6, N.v6.
  rewrite ?node_23205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23207 (s : N.State) (i : N.Inputs) :
  R.v23207 (state s) (inputs i) = Zmod.unsigned (N.v23207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23207 s i)) at 1.
  unfold R.v23207, N.v23207.
  rewrite ?node_8461.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23208 (s : N.State) (i : N.Inputs) :
  R.v23208 (state s) (inputs i) = Zmod.unsigned (N.v23208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23208 s i)) at 1.
  unfold R.v23208, N.v23208.
  unfold R.v6, N.v6.
  rewrite ?node_8589.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23209 (s : N.State) (i : N.Inputs) :
  R.v23209 (state s) (inputs i) = Zmod.unsigned (N.v23209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23209 s i)) at 1.
  unfold R.v23209, N.v23209.
  unfold R.v6, N.v6.
  rewrite ?node_8625.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23210 (s : N.State) (i : N.Inputs) :
  R.v23210 (state s) (inputs i) = Zmod.unsigned (N.v23210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23210 s i)) at 1.
  unfold R.v23210, N.v23210.
  rewrite ?node_23207.
  rewrite ?node_23208.
  rewrite ?node_23209.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23211 (s : N.State) (i : N.Inputs) :
  R.v23211 (state s) (inputs i) = Zmod.unsigned (N.v23211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23211 s i)) at 1.
  unfold R.v23211, N.v23211.
  rewrite ?node_23206.
  rewrite ?node_23210.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23212 (s : N.State) (i : N.Inputs) :
  R.v23212 (state s) (inputs i) = Zmod.unsigned (N.v23212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23212 s i)) at 1.
  unfold R.v23212, N.v23212.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23213 (s : N.State) (i : N.Inputs) :
  R.v23213 (state s) (inputs i) = Zmod.unsigned (N.v23213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23213 s i)) at 1.
  unfold R.v23213, N.v23213.
  unfold R.v16463, N.v16463.
  rewrite !state_r745_nr_5F745.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r745_nr_5F745 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23214 (s : N.State) (i : N.Inputs) :
  R.v23214 (state s) (inputs i) = Zmod.unsigned (N.v23214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23214 s i)) at 1.
  unfold R.v23214, N.v23214.
  unfold R.v6, N.v6.
  rewrite !state_r744_nr_5F744.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r744_nr_5F744 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23215 (s : N.State) (i : N.Inputs) :
  R.v23215 (state s) (inputs i) = Zmod.unsigned (N.v23215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23215 s i)) at 1.
  unfold R.v23215, N.v23215.
  unfold R.v6, N.v6.
  rewrite !state_r743_nr_5F743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r743_nr_5F743 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23216 (s : N.State) (i : N.Inputs) :
  R.v23216 (state s) (inputs i) = Zmod.unsigned (N.v23216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23216 s i)) at 1.
  unfold R.v23216, N.v23216.
  rewrite ?node_23214.
  rewrite ?node_23215.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23217 (s : N.State) (i : N.Inputs) :
  R.v23217 (state s) (inputs i) = Zmod.unsigned (N.v23217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23217 s i)) at 1.
  unfold R.v23217, N.v23217.
  unfold R.v16484, N.v16484.
  rewrite ?node_23216.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23218 (s : N.State) (i : N.Inputs) :
  R.v23218 (state s) (inputs i) = Zmod.unsigned (N.v23218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23218 s i)) at 1.
  unfold R.v23218, N.v23218.
  rewrite ?node_23213.
  rewrite ?node_23217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23219 (s : N.State) (i : N.Inputs) :
  R.v23219 (state s) (inputs i) = Zmod.unsigned (N.v23219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23219 s i)) at 1.
  unfold R.v23219, N.v23219.
  unfold R.v6, N.v6.
  rewrite ?node_23218.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23220 (s : N.State) (i : N.Inputs) :
  R.v23220 (state s) (inputs i) = Zmod.unsigned (N.v23220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23220 s i)) at 1.
  unfold R.v23220, N.v23220.
  rewrite ?node_8456.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23221 (s : N.State) (i : N.Inputs) :
  R.v23221 (state s) (inputs i) = Zmod.unsigned (N.v23221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23221 s i)) at 1.
  unfold R.v23221, N.v23221.
  unfold R.v6, N.v6.
  rewrite ?node_8589.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23222 (s : N.State) (i : N.Inputs) :
  R.v23222 (state s) (inputs i) = Zmod.unsigned (N.v23222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23222 s i)) at 1.
  unfold R.v23222, N.v23222.
  rewrite ?node_23220.
  rewrite ?node_23221.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23223 (s : N.State) (i : N.Inputs) :
  R.v23223 (state s) (inputs i) = Zmod.unsigned (N.v23223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23223 s i)) at 1.
  unfold R.v23223, N.v23223.
  rewrite ?node_23219.
  rewrite ?node_23222.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23224 (s : N.State) (i : N.Inputs) :
  R.v23224 (state s) (inputs i) = Zmod.unsigned (N.v23224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23224 s i)) at 1.
  unfold R.v23224, N.v23224.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23225 (s : N.State) (i : N.Inputs) :
  R.v23225 (state s) (inputs i) = Zmod.unsigned (N.v23225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23225 s i)) at 1.
  unfold R.v23225, N.v23225.
  rewrite ?node_8460.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23226 (s : N.State) (i : N.Inputs) :
  R.v23226 (state s) (inputs i) = Zmod.unsigned (N.v23226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23226 s i)) at 1.
  unfold R.v23226, N.v23226.
  unfold R.v6, N.v6.
  rewrite !state_r746_nr_5F746.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r746_nr_5F746 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23227 (s : N.State) (i : N.Inputs) :
  R.v23227 (state s) (inputs i) = Zmod.unsigned (N.v23227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23227 s i)) at 1.
  unfold R.v23227, N.v23227.
  unfold R.v6, N.v6.
  rewrite ?node_8456.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23228 (s : N.State) (i : N.Inputs) :
  R.v23228 (state s) (inputs i) = Zmod.unsigned (N.v23228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23228 s i)) at 1.
  unfold R.v23228, N.v23228.
  rewrite ?node_23226.
  rewrite ?node_23227.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23229 (s : N.State) (i : N.Inputs) :
  R.v23229 (state s) (inputs i) = Zmod.unsigned (N.v23229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23229 s i)) at 1.
  unfold R.v23229, N.v23229.
  unfold R.v16484, N.v16484.
  rewrite ?node_23228.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23230 (s : N.State) (i : N.Inputs) :
  R.v23230 (state s) (inputs i) = Zmod.unsigned (N.v23230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23230 s i)) at 1.
  unfold R.v23230, N.v23230.
  rewrite ?node_23225.
  rewrite ?node_23229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23231 (s : N.State) (i : N.Inputs) :
  R.v23231 (state s) (inputs i) = Zmod.unsigned (N.v23231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23231 s i)) at 1.
  unfold R.v23231, N.v23231.
  unfold R.v6, N.v6.
  rewrite ?node_23230.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23232 (s : N.State) (i : N.Inputs) :
  R.v23232 (state s) (inputs i) = Zmod.unsigned (N.v23232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23232 s i)) at 1.
  unfold R.v23232, N.v23232.
  rewrite ?node_8461.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23233 (s : N.State) (i : N.Inputs) :
  R.v23233 (state s) (inputs i) = Zmod.unsigned (N.v23233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23233 s i)) at 1.
  unfold R.v23233, N.v23233.
  unfold R.v6, N.v6.
  rewrite ?node_8625.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23234 (s : N.State) (i : N.Inputs) :
  R.v23234 (state s) (inputs i) = Zmod.unsigned (N.v23234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23234 s i)) at 1.
  unfold R.v23234, N.v23234.
  rewrite ?node_23232.
  rewrite ?node_23233.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23235 (s : N.State) (i : N.Inputs) :
  R.v23235 (state s) (inputs i) = Zmod.unsigned (N.v23235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23235 s i)) at 1.
  unfold R.v23235, N.v23235.
  rewrite ?node_23231.
  rewrite ?node_23234.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23236 (s : N.State) (i : N.Inputs) :
  R.v23236 (state s) (inputs i) = Zmod.unsigned (N.v23236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23236 s i)) at 1.
  unfold R.v23236, N.v23236.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23237 (s : N.State) (i : N.Inputs) :
  R.v23237 (state s) (inputs i) = Zmod.unsigned (N.v23237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23237 s i)) at 1.
  unfold R.v23237, N.v23237.
  rewrite ?node_8467.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23238 (s : N.State) (i : N.Inputs) :
  R.v23238 (state s) (inputs i) = Zmod.unsigned (N.v23238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23238 s i)) at 1.
  unfold R.v23238, N.v23238.
  unfold R.v16463, N.v16463.
  rewrite !state_r750_nr_5F750.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r750_nr_5F750 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23239 (s : N.State) (i : N.Inputs) :
  R.v23239 (state s) (inputs i) = Zmod.unsigned (N.v23239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23239 s i)) at 1.
  unfold R.v23239, N.v23239.
  unfold R.v16463, N.v16463.
  rewrite !state_r749_nr_5F749.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r749_nr_5F749 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23240 (s : N.State) (i : N.Inputs) :
  R.v23240 (state s) (inputs i) = Zmod.unsigned (N.v23240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23240 s i)) at 1.
  unfold R.v23240, N.v23240.
  unfold R.v6, N.v6.
  rewrite !state_r748_nr_5F748.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r748_nr_5F748 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23241 (s : N.State) (i : N.Inputs) :
  R.v23241 (state s) (inputs i) = Zmod.unsigned (N.v23241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23241 s i)) at 1.
  unfold R.v23241, N.v23241.
  unfold R.v6, N.v6.
  rewrite !state_r747_nr_5F747.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r747_nr_5F747 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23242 (s : N.State) (i : N.Inputs) :
  R.v23242 (state s) (inputs i) = Zmod.unsigned (N.v23242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23242 s i)) at 1.
  unfold R.v23242, N.v23242.
  rewrite ?node_23240.
  rewrite ?node_23241.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23243 (s : N.State) (i : N.Inputs) :
  R.v23243 (state s) (inputs i) = Zmod.unsigned (N.v23243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23243 s i)) at 1.
  unfold R.v23243, N.v23243.
  unfold R.v16484, N.v16484.
  rewrite ?node_23242.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23244 (s : N.State) (i : N.Inputs) :
  R.v23244 (state s) (inputs i) = Zmod.unsigned (N.v23244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23244 s i)) at 1.
  unfold R.v23244, N.v23244.
  rewrite ?node_23237.
  rewrite ?node_23238.
  rewrite ?node_23239.
  rewrite ?node_23243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23245 (s : N.State) (i : N.Inputs) :
  R.v23245 (state s) (inputs i) = Zmod.unsigned (N.v23245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23245 s i)) at 1.
  unfold R.v23245, N.v23245.
  unfold R.v6, N.v6.
  rewrite ?node_23244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23246 (s : N.State) (i : N.Inputs) :
  R.v23246 (state s) (inputs i) = Zmod.unsigned (N.v23246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23246 s i)) at 1.
  unfold R.v23246, N.v23246.
  rewrite ?node_8468.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23247 (s : N.State) (i : N.Inputs) :
  R.v23247 (state s) (inputs i) = Zmod.unsigned (N.v23247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23247 s i)) at 1.
  unfold R.v23247, N.v23247.
  unfold R.v6, N.v6.
  rewrite ?node_8596.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23248 (s : N.State) (i : N.Inputs) :
  R.v23248 (state s) (inputs i) = Zmod.unsigned (N.v23248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23248 s i)) at 1.
  unfold R.v23248, N.v23248.
  unfold R.v6, N.v6.
  rewrite ?node_8634.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23249 (s : N.State) (i : N.Inputs) :
  R.v23249 (state s) (inputs i) = Zmod.unsigned (N.v23249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23249 s i)) at 1.
  unfold R.v23249, N.v23249.
  rewrite ?node_23246.
  rewrite ?node_23247.
  rewrite ?node_23248.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23250 (s : N.State) (i : N.Inputs) :
  R.v23250 (state s) (inputs i) = Zmod.unsigned (N.v23250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23250 s i)) at 1.
  unfold R.v23250, N.v23250.
  rewrite ?node_23245.
  rewrite ?node_23249.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23251 (s : N.State) (i : N.Inputs) :
  R.v23251 (state s) (inputs i) = Zmod.unsigned (N.v23251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23251 s i)) at 1.
  unfold R.v23251, N.v23251.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23252 (s : N.State) (i : N.Inputs) :
  R.v23252 (state s) (inputs i) = Zmod.unsigned (N.v23252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23252 s i)) at 1.
  unfold R.v23252, N.v23252.
  unfold R.v16463, N.v16463.
  rewrite !state_r749_nr_5F749.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r749_nr_5F749 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23253 (s : N.State) (i : N.Inputs) :
  R.v23253 (state s) (inputs i) = Zmod.unsigned (N.v23253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23253 s i)) at 1.
  unfold R.v23253, N.v23253.
  unfold R.v6, N.v6.
  rewrite !state_r748_nr_5F748.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r748_nr_5F748 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23254 (s : N.State) (i : N.Inputs) :
  R.v23254 (state s) (inputs i) = Zmod.unsigned (N.v23254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23254 s i)) at 1.
  unfold R.v23254, N.v23254.
  unfold R.v6, N.v6.
  rewrite !state_r747_nr_5F747.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r747_nr_5F747 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23255 (s : N.State) (i : N.Inputs) :
  R.v23255 (state s) (inputs i) = Zmod.unsigned (N.v23255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23255 s i)) at 1.
  unfold R.v23255, N.v23255.
  rewrite ?node_23253.
  rewrite ?node_23254.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23256 (s : N.State) (i : N.Inputs) :
  R.v23256 (state s) (inputs i) = Zmod.unsigned (N.v23256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23256 s i)) at 1.
  unfold R.v23256, N.v23256.
  unfold R.v16484, N.v16484.
  rewrite ?node_23255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23257 (s : N.State) (i : N.Inputs) :
  R.v23257 (state s) (inputs i) = Zmod.unsigned (N.v23257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23257 s i)) at 1.
  unfold R.v23257, N.v23257.
  rewrite ?node_23252.
  rewrite ?node_23256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23258 (s : N.State) (i : N.Inputs) :
  R.v23258 (state s) (inputs i) = Zmod.unsigned (N.v23258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23258 s i)) at 1.
  unfold R.v23258, N.v23258.
  unfold R.v6, N.v6.
  rewrite ?node_23257.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23259 (s : N.State) (i : N.Inputs) :
  R.v23259 (state s) (inputs i) = Zmod.unsigned (N.v23259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23259 s i)) at 1.
  unfold R.v23259, N.v23259.
  rewrite ?node_8463.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23260 (s : N.State) (i : N.Inputs) :
  R.v23260 (state s) (inputs i) = Zmod.unsigned (N.v23260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23260 s i)) at 1.
  unfold R.v23260, N.v23260.
  unfold R.v6, N.v6.
  rewrite ?node_8596.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23261 (s : N.State) (i : N.Inputs) :
  R.v23261 (state s) (inputs i) = Zmod.unsigned (N.v23261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23261 s i)) at 1.
  unfold R.v23261, N.v23261.
  rewrite ?node_23259.
  rewrite ?node_23260.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23262 (s : N.State) (i : N.Inputs) :
  R.v23262 (state s) (inputs i) = Zmod.unsigned (N.v23262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23262 s i)) at 1.
  unfold R.v23262, N.v23262.
  rewrite ?node_23258.
  rewrite ?node_23261.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23263 (s : N.State) (i : N.Inputs) :
  R.v23263 (state s) (inputs i) = Zmod.unsigned (N.v23263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23263 s i)) at 1.
  unfold R.v23263, N.v23263.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23264 (s : N.State) (i : N.Inputs) :
  R.v23264 (state s) (inputs i) = Zmod.unsigned (N.v23264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23264 s i)) at 1.
  unfold R.v23264, N.v23264.
  rewrite ?node_8467.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23265 (s : N.State) (i : N.Inputs) :
  R.v23265 (state s) (inputs i) = Zmod.unsigned (N.v23265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23265 s i)) at 1.
  unfold R.v23265, N.v23265.
  unfold R.v6, N.v6.
  rewrite !state_r750_nr_5F750.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r750_nr_5F750 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23266 (s : N.State) (i : N.Inputs) :
  R.v23266 (state s) (inputs i) = Zmod.unsigned (N.v23266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23266 s i)) at 1.
  unfold R.v23266, N.v23266.
  unfold R.v6, N.v6.
  rewrite ?node_8463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23267 (s : N.State) (i : N.Inputs) :
  R.v23267 (state s) (inputs i) = Zmod.unsigned (N.v23267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23267 s i)) at 1.
  unfold R.v23267, N.v23267.
  rewrite ?node_23265.
  rewrite ?node_23266.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23268 (s : N.State) (i : N.Inputs) :
  R.v23268 (state s) (inputs i) = Zmod.unsigned (N.v23268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23268 s i)) at 1.
  unfold R.v23268, N.v23268.
  unfold R.v16484, N.v16484.
  rewrite ?node_23267.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23269 (s : N.State) (i : N.Inputs) :
  R.v23269 (state s) (inputs i) = Zmod.unsigned (N.v23269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23269 s i)) at 1.
  unfold R.v23269, N.v23269.
  rewrite ?node_23264.
  rewrite ?node_23268.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23270 (s : N.State) (i : N.Inputs) :
  R.v23270 (state s) (inputs i) = Zmod.unsigned (N.v23270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23270 s i)) at 1.
  unfold R.v23270, N.v23270.
  unfold R.v6, N.v6.
  rewrite ?node_23269.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23271 (s : N.State) (i : N.Inputs) :
  R.v23271 (state s) (inputs i) = Zmod.unsigned (N.v23271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23271 s i)) at 1.
  unfold R.v23271, N.v23271.
  rewrite ?node_8468.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23272 (s : N.State) (i : N.Inputs) :
  R.v23272 (state s) (inputs i) = Zmod.unsigned (N.v23272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23272 s i)) at 1.
  unfold R.v23272, N.v23272.
  unfold R.v6, N.v6.
  rewrite ?node_8634.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23273 (s : N.State) (i : N.Inputs) :
  R.v23273 (state s) (inputs i) = Zmod.unsigned (N.v23273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23273 s i)) at 1.
  unfold R.v23273, N.v23273.
  rewrite ?node_23271.
  rewrite ?node_23272.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23274 (s : N.State) (i : N.Inputs) :
  R.v23274 (state s) (inputs i) = Zmod.unsigned (N.v23274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23274 s i)) at 1.
  unfold R.v23274, N.v23274.
  rewrite ?node_23270.
  rewrite ?node_23273.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23275 (s : N.State) (i : N.Inputs) :
  R.v23275 (state s) (inputs i) = Zmod.unsigned (N.v23275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23275 s i)) at 1.
  unfold R.v23275, N.v23275.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23276 (s : N.State) (i : N.Inputs) :
  R.v23276 (state s) (inputs i) = Zmod.unsigned (N.v23276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23276 s i)) at 1.
  unfold R.v23276, N.v23276.
  unfold R.v16463, N.v16463.
  rewrite !state_r753_nr_5F753.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r753_nr_5F753 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23277 (s : N.State) (i : N.Inputs) :
  R.v23277 (state s) (inputs i) = Zmod.unsigned (N.v23277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23277 s i)) at 1.
  unfold R.v23277, N.v23277.
  unfold R.v6, N.v6.
  rewrite !state_r752_nr_5F752.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r752_nr_5F752 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23278 (s : N.State) (i : N.Inputs) :
  R.v23278 (state s) (inputs i) = Zmod.unsigned (N.v23278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23278 s i)) at 1.
  unfold R.v23278, N.v23278.
  unfold R.v6, N.v6.
  rewrite !state_r751_nr_5F751.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r751_nr_5F751 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23279 (s : N.State) (i : N.Inputs) :
  R.v23279 (state s) (inputs i) = Zmod.unsigned (N.v23279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23279 s i)) at 1.
  unfold R.v23279, N.v23279.
  rewrite ?node_23277.
  rewrite ?node_23278.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23280 (s : N.State) (i : N.Inputs) :
  R.v23280 (state s) (inputs i) = Zmod.unsigned (N.v23280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23280 s i)) at 1.
  unfold R.v23280, N.v23280.
  unfold R.v16484, N.v16484.
  rewrite ?node_23279.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23281 (s : N.State) (i : N.Inputs) :
  R.v23281 (state s) (inputs i) = Zmod.unsigned (N.v23281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23281 s i)) at 1.
  unfold R.v23281, N.v23281.
  rewrite ?node_23276.
  rewrite ?node_23280.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23282 (s : N.State) (i : N.Inputs) :
  R.v23282 (state s) (inputs i) = Zmod.unsigned (N.v23282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23282 s i)) at 1.
  unfold R.v23282, N.v23282.
  unfold R.v6, N.v6.
  rewrite ?node_23281.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23283 (s : N.State) (i : N.Inputs) :
  R.v23283 (state s) (inputs i) = Zmod.unsigned (N.v23283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23283 s i)) at 1.
  unfold R.v23283, N.v23283.
  rewrite ?node_8471.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23284 (s : N.State) (i : N.Inputs) :
  R.v23284 (state s) (inputs i) = Zmod.unsigned (N.v23284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23284 s i)) at 1.
  unfold R.v23284, N.v23284.
  unfold R.v6, N.v6.
  rewrite ?node_8637.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23285 (s : N.State) (i : N.Inputs) :
  R.v23285 (state s) (inputs i) = Zmod.unsigned (N.v23285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23285 s i)) at 1.
  unfold R.v23285, N.v23285.
  rewrite ?node_23283.
  rewrite ?node_23284.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23286 (s : N.State) (i : N.Inputs) :
  R.v23286 (state s) (inputs i) = Zmod.unsigned (N.v23286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23286 s i)) at 1.
  unfold R.v23286, N.v23286.
  rewrite ?node_23282.
  rewrite ?node_23285.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23287 (s : N.State) (i : N.Inputs) :
  R.v23287 (state s) (inputs i) = Zmod.unsigned (N.v23287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23287 s i)) at 1.
  unfold R.v23287, N.v23287.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23288 (s : N.State) (i : N.Inputs) :
  R.v23288 (state s) (inputs i) = Zmod.unsigned (N.v23288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23288 s i)) at 1.
  unfold R.v23288, N.v23288.
  rewrite ?node_8554.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23289 (s : N.State) (i : N.Inputs) :
  R.v23289 (state s) (inputs i) = Zmod.unsigned (N.v23289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23289 s i)) at 1.
  unfold R.v23289, N.v23289.
  unfold R.v16463, N.v16463.
  rewrite !state_r757_nr_5F757.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r757_nr_5F757 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23290 (s : N.State) (i : N.Inputs) :
  R.v23290 (state s) (inputs i) = Zmod.unsigned (N.v23290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23290 s i)) at 1.
  unfold R.v23290, N.v23290.
  unfold R.v16463, N.v16463.
  rewrite !state_r756_nr_5F756.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r756_nr_5F756 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23291 (s : N.State) (i : N.Inputs) :
  R.v23291 (state s) (inputs i) = Zmod.unsigned (N.v23291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23291 s i)) at 1.
  unfold R.v23291, N.v23291.
  unfold R.v6, N.v6.
  rewrite !state_r755_nr_5F755.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r755_nr_5F755 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23292 (s : N.State) (i : N.Inputs) :
  R.v23292 (state s) (inputs i) = Zmod.unsigned (N.v23292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23292 s i)) at 1.
  unfold R.v23292, N.v23292.
  unfold R.v6, N.v6.
  rewrite !state_r754_nr_5F754.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r754_nr_5F754 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23293 (s : N.State) (i : N.Inputs) :
  R.v23293 (state s) (inputs i) = Zmod.unsigned (N.v23293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23293 s i)) at 1.
  unfold R.v23293, N.v23293.
  rewrite ?node_23291.
  rewrite ?node_23292.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23294 (s : N.State) (i : N.Inputs) :
  R.v23294 (state s) (inputs i) = Zmod.unsigned (N.v23294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23294 s i)) at 1.
  unfold R.v23294, N.v23294.
  unfold R.v16484, N.v16484.
  rewrite ?node_23293.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23295 (s : N.State) (i : N.Inputs) :
  R.v23295 (state s) (inputs i) = Zmod.unsigned (N.v23295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23295 s i)) at 1.
  unfold R.v23295, N.v23295.
  rewrite ?node_23288.
  rewrite ?node_23289.
  rewrite ?node_23290.
  rewrite ?node_23294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23296 (s : N.State) (i : N.Inputs) :
  R.v23296 (state s) (inputs i) = Zmod.unsigned (N.v23296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23296 s i)) at 1.
  unfold R.v23296, N.v23296.
  unfold R.v6, N.v6.
  rewrite ?node_23295.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23297 (s : N.State) (i : N.Inputs) :
  R.v23297 (state s) (inputs i) = Zmod.unsigned (N.v23297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23297 s i)) at 1.
  unfold R.v23297, N.v23297.
  rewrite ?node_8555.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23298 (s : N.State) (i : N.Inputs) :
  R.v23298 (state s) (inputs i) = Zmod.unsigned (N.v23298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23298 s i)) at 1.
  unfold R.v23298, N.v23298.
  unfold R.v6, N.v6.
  rewrite ?node_8686.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23299 (s : N.State) (i : N.Inputs) :
  R.v23299 (state s) (inputs i) = Zmod.unsigned (N.v23299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23299 s i)) at 1.
  unfold R.v23299, N.v23299.
  unfold R.v6, N.v6.
  rewrite ?node_8741.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23300 (s : N.State) (i : N.Inputs) :
  R.v23300 (state s) (inputs i) = Zmod.unsigned (N.v23300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23300 s i)) at 1.
  unfold R.v23300, N.v23300.
  rewrite ?node_23297.
  rewrite ?node_23298.
  rewrite ?node_23299.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23301 (s : N.State) (i : N.Inputs) :
  R.v23301 (state s) (inputs i) = Zmod.unsigned (N.v23301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23301 s i)) at 1.
  unfold R.v23301, N.v23301.
  rewrite ?node_23296.
  rewrite ?node_23300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23302 (s : N.State) (i : N.Inputs) :
  R.v23302 (state s) (inputs i) = Zmod.unsigned (N.v23302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23302 s i)) at 1.
  unfold R.v23302, N.v23302.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23303 (s : N.State) (i : N.Inputs) :
  R.v23303 (state s) (inputs i) = Zmod.unsigned (N.v23303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23303 s i)) at 1.
  unfold R.v23303, N.v23303.
  unfold R.v16463, N.v16463.
  rewrite !state_r756_nr_5F756.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r756_nr_5F756 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23304 (s : N.State) (i : N.Inputs) :
  R.v23304 (state s) (inputs i) = Zmod.unsigned (N.v23304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23304 s i)) at 1.
  unfold R.v23304, N.v23304.
  unfold R.v6, N.v6.
  rewrite !state_r755_nr_5F755.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r755_nr_5F755 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23305 (s : N.State) (i : N.Inputs) :
  R.v23305 (state s) (inputs i) = Zmod.unsigned (N.v23305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23305 s i)) at 1.
  unfold R.v23305, N.v23305.
  unfold R.v6, N.v6.
  rewrite !state_r754_nr_5F754.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r754_nr_5F754 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23306 (s : N.State) (i : N.Inputs) :
  R.v23306 (state s) (inputs i) = Zmod.unsigned (N.v23306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23306 s i)) at 1.
  unfold R.v23306, N.v23306.
  rewrite ?node_23304.
  rewrite ?node_23305.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23307 (s : N.State) (i : N.Inputs) :
  R.v23307 (state s) (inputs i) = Zmod.unsigned (N.v23307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23307 s i)) at 1.
  unfold R.v23307, N.v23307.
  unfold R.v16484, N.v16484.
  rewrite ?node_23306.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23308 (s : N.State) (i : N.Inputs) :
  R.v23308 (state s) (inputs i) = Zmod.unsigned (N.v23308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23308 s i)) at 1.
  unfold R.v23308, N.v23308.
  rewrite ?node_23303.
  rewrite ?node_23307.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23309 (s : N.State) (i : N.Inputs) :
  R.v23309 (state s) (inputs i) = Zmod.unsigned (N.v23309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23309 s i)) at 1.
  unfold R.v23309, N.v23309.
  unfold R.v6, N.v6.
  rewrite ?node_23308.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23310 (s : N.State) (i : N.Inputs) :
  R.v23310 (state s) (inputs i) = Zmod.unsigned (N.v23310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23310 s i)) at 1.
  unfold R.v23310, N.v23310.
  rewrite ?node_8550.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23311 (s : N.State) (i : N.Inputs) :
  R.v23311 (state s) (inputs i) = Zmod.unsigned (N.v23311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23311 s i)) at 1.
  unfold R.v23311, N.v23311.
  unfold R.v6, N.v6.
  rewrite ?node_8686.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23312 (s : N.State) (i : N.Inputs) :
  R.v23312 (state s) (inputs i) = Zmod.unsigned (N.v23312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23312 s i)) at 1.
  unfold R.v23312, N.v23312.
  rewrite ?node_23310.
  rewrite ?node_23311.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23313 (s : N.State) (i : N.Inputs) :
  R.v23313 (state s) (inputs i) = Zmod.unsigned (N.v23313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23313 s i)) at 1.
  unfold R.v23313, N.v23313.
  rewrite ?node_23309.
  rewrite ?node_23312.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23314 (s : N.State) (i : N.Inputs) :
  R.v23314 (state s) (inputs i) = Zmod.unsigned (N.v23314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23314 s i)) at 1.
  unfold R.v23314, N.v23314.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23315 (s : N.State) (i : N.Inputs) :
  R.v23315 (state s) (inputs i) = Zmod.unsigned (N.v23315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23315 s i)) at 1.
  unfold R.v23315, N.v23315.
  rewrite ?node_8554.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23316 (s : N.State) (i : N.Inputs) :
  R.v23316 (state s) (inputs i) = Zmod.unsigned (N.v23316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23316 s i)) at 1.
  unfold R.v23316, N.v23316.
  unfold R.v6, N.v6.
  rewrite !state_r757_nr_5F757.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r757_nr_5F757 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23317 (s : N.State) (i : N.Inputs) :
  R.v23317 (state s) (inputs i) = Zmod.unsigned (N.v23317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23317 s i)) at 1.
  unfold R.v23317, N.v23317.
  unfold R.v6, N.v6.
  rewrite ?node_8550.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23318 (s : N.State) (i : N.Inputs) :
  R.v23318 (state s) (inputs i) = Zmod.unsigned (N.v23318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23318 s i)) at 1.
  unfold R.v23318, N.v23318.
  rewrite ?node_23316.
  rewrite ?node_23317.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23319 (s : N.State) (i : N.Inputs) :
  R.v23319 (state s) (inputs i) = Zmod.unsigned (N.v23319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23319 s i)) at 1.
  unfold R.v23319, N.v23319.
  unfold R.v16484, N.v16484.
  rewrite ?node_23318.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23320 (s : N.State) (i : N.Inputs) :
  R.v23320 (state s) (inputs i) = Zmod.unsigned (N.v23320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23320 s i)) at 1.
  unfold R.v23320, N.v23320.
  rewrite ?node_23315.
  rewrite ?node_23319.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23321 (s : N.State) (i : N.Inputs) :
  R.v23321 (state s) (inputs i) = Zmod.unsigned (N.v23321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23321 s i)) at 1.
  unfold R.v23321, N.v23321.
  unfold R.v6, N.v6.
  rewrite ?node_23320.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23322 (s : N.State) (i : N.Inputs) :
  R.v23322 (state s) (inputs i) = Zmod.unsigned (N.v23322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23322 s i)) at 1.
  unfold R.v23322, N.v23322.
  rewrite ?node_8555.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23323 (s : N.State) (i : N.Inputs) :
  R.v23323 (state s) (inputs i) = Zmod.unsigned (N.v23323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23323 s i)) at 1.
  unfold R.v23323, N.v23323.
  unfold R.v6, N.v6.
  rewrite ?node_8741.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23324 (s : N.State) (i : N.Inputs) :
  R.v23324 (state s) (inputs i) = Zmod.unsigned (N.v23324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23324 s i)) at 1.
  unfold R.v23324, N.v23324.
  rewrite ?node_23322.
  rewrite ?node_23323.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23325 (s : N.State) (i : N.Inputs) :
  R.v23325 (state s) (inputs i) = Zmod.unsigned (N.v23325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23325 s i)) at 1.
  unfold R.v23325, N.v23325.
  rewrite ?node_23321.
  rewrite ?node_23324.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23326 (s : N.State) (i : N.Inputs) :
  R.v23326 (state s) (inputs i) = Zmod.unsigned (N.v23326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23326 s i)) at 1.
  unfold R.v23326, N.v23326.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23327 (s : N.State) (i : N.Inputs) :
  R.v23327 (state s) (inputs i) = Zmod.unsigned (N.v23327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23327 s i)) at 1.
  unfold R.v23327, N.v23327.
  rewrite ?node_8561.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23328 (s : N.State) (i : N.Inputs) :
  R.v23328 (state s) (inputs i) = Zmod.unsigned (N.v23328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23328 s i)) at 1.
  unfold R.v23328, N.v23328.
  unfold R.v16463, N.v16463.
  rewrite !state_r761_nr_5F761.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r761_nr_5F761 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23329 (s : N.State) (i : N.Inputs) :
  R.v23329 (state s) (inputs i) = Zmod.unsigned (N.v23329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23329 s i)) at 1.
  unfold R.v23329, N.v23329.
  unfold R.v16463, N.v16463.
  rewrite !state_r760_nr_5F760.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r760_nr_5F760 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23330 (s : N.State) (i : N.Inputs) :
  R.v23330 (state s) (inputs i) = Zmod.unsigned (N.v23330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23330 s i)) at 1.
  unfold R.v23330, N.v23330.
  unfold R.v6, N.v6.
  rewrite !state_r759_nr_5F759.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r759_nr_5F759 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23331 (s : N.State) (i : N.Inputs) :
  R.v23331 (state s) (inputs i) = Zmod.unsigned (N.v23331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23331 s i)) at 1.
  unfold R.v23331, N.v23331.
  unfold R.v6, N.v6.
  rewrite !state_r758_nr_5F758.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r758_nr_5F758 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23332 (s : N.State) (i : N.Inputs) :
  R.v23332 (state s) (inputs i) = Zmod.unsigned (N.v23332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23332 s i)) at 1.
  unfold R.v23332, N.v23332.
  rewrite ?node_23330.
  rewrite ?node_23331.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23333 (s : N.State) (i : N.Inputs) :
  R.v23333 (state s) (inputs i) = Zmod.unsigned (N.v23333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23333 s i)) at 1.
  unfold R.v23333, N.v23333.
  unfold R.v16484, N.v16484.
  rewrite ?node_23332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23334 (s : N.State) (i : N.Inputs) :
  R.v23334 (state s) (inputs i) = Zmod.unsigned (N.v23334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23334 s i)) at 1.
  unfold R.v23334, N.v23334.
  rewrite ?node_23327.
  rewrite ?node_23328.
  rewrite ?node_23329.
  rewrite ?node_23333.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23335 (s : N.State) (i : N.Inputs) :
  R.v23335 (state s) (inputs i) = Zmod.unsigned (N.v23335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23335 s i)) at 1.
  unfold R.v23335, N.v23335.
  unfold R.v6, N.v6.
  rewrite ?node_23334.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23336 (s : N.State) (i : N.Inputs) :
  R.v23336 (state s) (inputs i) = Zmod.unsigned (N.v23336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23336 s i)) at 1.
  unfold R.v23336, N.v23336.
  rewrite ?node_8562.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23337 (s : N.State) (i : N.Inputs) :
  R.v23337 (state s) (inputs i) = Zmod.unsigned (N.v23337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23337 s i)) at 1.
  unfold R.v23337, N.v23337.
  unfold R.v6, N.v6.
  rewrite ?node_8693.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23338 (s : N.State) (i : N.Inputs) :
  R.v23338 (state s) (inputs i) = Zmod.unsigned (N.v23338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23338 s i)) at 1.
  unfold R.v23338, N.v23338.
  unfold R.v6, N.v6.
  rewrite ?node_8750.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23339 (s : N.State) (i : N.Inputs) :
  R.v23339 (state s) (inputs i) = Zmod.unsigned (N.v23339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23339 s i)) at 1.
  unfold R.v23339, N.v23339.
  rewrite ?node_23336.
  rewrite ?node_23337.
  rewrite ?node_23338.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23340 (s : N.State) (i : N.Inputs) :
  R.v23340 (state s) (inputs i) = Zmod.unsigned (N.v23340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23340 s i)) at 1.
  unfold R.v23340, N.v23340.
  rewrite ?node_23335.
  rewrite ?node_23339.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23341 (s : N.State) (i : N.Inputs) :
  R.v23341 (state s) (inputs i) = Zmod.unsigned (N.v23341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23341 s i)) at 1.
  unfold R.v23341, N.v23341.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23342 (s : N.State) (i : N.Inputs) :
  R.v23342 (state s) (inputs i) = Zmod.unsigned (N.v23342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23342 s i)) at 1.
  unfold R.v23342, N.v23342.
  unfold R.v16463, N.v16463.
  rewrite !state_r760_nr_5F760.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r760_nr_5F760 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23343 (s : N.State) (i : N.Inputs) :
  R.v23343 (state s) (inputs i) = Zmod.unsigned (N.v23343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23343 s i)) at 1.
  unfold R.v23343, N.v23343.
  unfold R.v6, N.v6.
  rewrite !state_r759_nr_5F759.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r759_nr_5F759 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23344 (s : N.State) (i : N.Inputs) :
  R.v23344 (state s) (inputs i) = Zmod.unsigned (N.v23344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23344 s i)) at 1.
  unfold R.v23344, N.v23344.
  unfold R.v6, N.v6.
  rewrite !state_r758_nr_5F758.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r758_nr_5F758 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23345 (s : N.State) (i : N.Inputs) :
  R.v23345 (state s) (inputs i) = Zmod.unsigned (N.v23345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23345 s i)) at 1.
  unfold R.v23345, N.v23345.
  rewrite ?node_23343.
  rewrite ?node_23344.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23346 (s : N.State) (i : N.Inputs) :
  R.v23346 (state s) (inputs i) = Zmod.unsigned (N.v23346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23346 s i)) at 1.
  unfold R.v23346, N.v23346.
  unfold R.v16484, N.v16484.
  rewrite ?node_23345.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23347 (s : N.State) (i : N.Inputs) :
  R.v23347 (state s) (inputs i) = Zmod.unsigned (N.v23347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23347 s i)) at 1.
  unfold R.v23347, N.v23347.
  rewrite ?node_23342.
  rewrite ?node_23346.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23348 (s : N.State) (i : N.Inputs) :
  R.v23348 (state s) (inputs i) = Zmod.unsigned (N.v23348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23348 s i)) at 1.
  unfold R.v23348, N.v23348.
  unfold R.v6, N.v6.
  rewrite ?node_23347.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23349 (s : N.State) (i : N.Inputs) :
  R.v23349 (state s) (inputs i) = Zmod.unsigned (N.v23349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23349 s i)) at 1.
  unfold R.v23349, N.v23349.
  rewrite ?node_8557.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23350 (s : N.State) (i : N.Inputs) :
  R.v23350 (state s) (inputs i) = Zmod.unsigned (N.v23350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23350 s i)) at 1.
  unfold R.v23350, N.v23350.
  unfold R.v6, N.v6.
  rewrite ?node_8693.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23351 (s : N.State) (i : N.Inputs) :
  R.v23351 (state s) (inputs i) = Zmod.unsigned (N.v23351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23351 s i)) at 1.
  unfold R.v23351, N.v23351.
  rewrite ?node_23349.
  rewrite ?node_23350.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23352 (s : N.State) (i : N.Inputs) :
  R.v23352 (state s) (inputs i) = Zmod.unsigned (N.v23352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23352 s i)) at 1.
  unfold R.v23352, N.v23352.
  rewrite ?node_23348.
  rewrite ?node_23351.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23353 (s : N.State) (i : N.Inputs) :
  R.v23353 (state s) (inputs i) = Zmod.unsigned (N.v23353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23353 s i)) at 1.
  unfold R.v23353, N.v23353.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23354 (s : N.State) (i : N.Inputs) :
  R.v23354 (state s) (inputs i) = Zmod.unsigned (N.v23354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23354 s i)) at 1.
  unfold R.v23354, N.v23354.
  rewrite ?node_8561.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23355 (s : N.State) (i : N.Inputs) :
  R.v23355 (state s) (inputs i) = Zmod.unsigned (N.v23355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23355 s i)) at 1.
  unfold R.v23355, N.v23355.
  unfold R.v6, N.v6.
  rewrite !state_r761_nr_5F761.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r761_nr_5F761 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23356 (s : N.State) (i : N.Inputs) :
  R.v23356 (state s) (inputs i) = Zmod.unsigned (N.v23356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23356 s i)) at 1.
  unfold R.v23356, N.v23356.
  unfold R.v6, N.v6.
  rewrite ?node_8557.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23357 (s : N.State) (i : N.Inputs) :
  R.v23357 (state s) (inputs i) = Zmod.unsigned (N.v23357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23357 s i)) at 1.
  unfold R.v23357, N.v23357.
  rewrite ?node_23355.
  rewrite ?node_23356.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23358 (s : N.State) (i : N.Inputs) :
  R.v23358 (state s) (inputs i) = Zmod.unsigned (N.v23358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23358 s i)) at 1.
  unfold R.v23358, N.v23358.
  unfold R.v16484, N.v16484.
  rewrite ?node_23357.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23359 (s : N.State) (i : N.Inputs) :
  R.v23359 (state s) (inputs i) = Zmod.unsigned (N.v23359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23359 s i)) at 1.
  unfold R.v23359, N.v23359.
  rewrite ?node_23354.
  rewrite ?node_23358.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23360 (s : N.State) (i : N.Inputs) :
  R.v23360 (state s) (inputs i) = Zmod.unsigned (N.v23360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23360 s i)) at 1.
  unfold R.v23360, N.v23360.
  unfold R.v6, N.v6.
  rewrite ?node_23359.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23361 (s : N.State) (i : N.Inputs) :
  R.v23361 (state s) (inputs i) = Zmod.unsigned (N.v23361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23361 s i)) at 1.
  unfold R.v23361, N.v23361.
  rewrite ?node_8562.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23362 (s : N.State) (i : N.Inputs) :
  R.v23362 (state s) (inputs i) = Zmod.unsigned (N.v23362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23362 s i)) at 1.
  unfold R.v23362, N.v23362.
  unfold R.v6, N.v6.
  rewrite ?node_8750.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23363 (s : N.State) (i : N.Inputs) :
  R.v23363 (state s) (inputs i) = Zmod.unsigned (N.v23363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23363 s i)) at 1.
  unfold R.v23363, N.v23363.
  rewrite ?node_23361.
  rewrite ?node_23362.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23364 (s : N.State) (i : N.Inputs) :
  R.v23364 (state s) (inputs i) = Zmod.unsigned (N.v23364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23364 s i)) at 1.
  unfold R.v23364, N.v23364.
  rewrite ?node_23360.
  rewrite ?node_23363.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23365 (s : N.State) (i : N.Inputs) :
  R.v23365 (state s) (inputs i) = Zmod.unsigned (N.v23365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23365 s i)) at 1.
  unfold R.v23365, N.v23365.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23366 (s : N.State) (i : N.Inputs) :
  R.v23366 (state s) (inputs i) = Zmod.unsigned (N.v23366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23366 s i)) at 1.
  unfold R.v23366, N.v23366.
  rewrite ?node_8569.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23367 (s : N.State) (i : N.Inputs) :
  R.v23367 (state s) (inputs i) = Zmod.unsigned (N.v23367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23367 s i)) at 1.
  unfold R.v23367, N.v23367.
  unfold R.v16463, N.v16463.
  rewrite !state_r765_nr_5F765.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r765_nr_5F765 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23368 (s : N.State) (i : N.Inputs) :
  R.v23368 (state s) (inputs i) = Zmod.unsigned (N.v23368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23368 s i)) at 1.
  unfold R.v23368, N.v23368.
  unfold R.v16463, N.v16463.
  rewrite !state_r764_nr_5F764.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r764_nr_5F764 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23369 (s : N.State) (i : N.Inputs) :
  R.v23369 (state s) (inputs i) = Zmod.unsigned (N.v23369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23369 s i)) at 1.
  unfold R.v23369, N.v23369.
  unfold R.v6, N.v6.
  rewrite !state_r763_nr_5F763.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r763_nr_5F763 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23370 (s : N.State) (i : N.Inputs) :
  R.v23370 (state s) (inputs i) = Zmod.unsigned (N.v23370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23370 s i)) at 1.
  unfold R.v23370, N.v23370.
  unfold R.v6, N.v6.
  rewrite !state_r762_nr_5F762.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r762_nr_5F762 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23371 (s : N.State) (i : N.Inputs) :
  R.v23371 (state s) (inputs i) = Zmod.unsigned (N.v23371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23371 s i)) at 1.
  unfold R.v23371, N.v23371.
  rewrite ?node_23369.
  rewrite ?node_23370.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23372 (s : N.State) (i : N.Inputs) :
  R.v23372 (state s) (inputs i) = Zmod.unsigned (N.v23372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23372 s i)) at 1.
  unfold R.v23372, N.v23372.
  unfold R.v16484, N.v16484.
  rewrite ?node_23371.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23373 (s : N.State) (i : N.Inputs) :
  R.v23373 (state s) (inputs i) = Zmod.unsigned (N.v23373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23373 s i)) at 1.
  unfold R.v23373, N.v23373.
  rewrite ?node_23366.
  rewrite ?node_23367.
  rewrite ?node_23368.
  rewrite ?node_23372.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23374 (s : N.State) (i : N.Inputs) :
  R.v23374 (state s) (inputs i) = Zmod.unsigned (N.v23374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23374 s i)) at 1.
  unfold R.v23374, N.v23374.
  unfold R.v6, N.v6.
  rewrite ?node_23373.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23375 (s : N.State) (i : N.Inputs) :
  R.v23375 (state s) (inputs i) = Zmod.unsigned (N.v23375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23375 s i)) at 1.
  unfold R.v23375, N.v23375.
  rewrite ?node_8570.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23376 (s : N.State) (i : N.Inputs) :
  R.v23376 (state s) (inputs i) = Zmod.unsigned (N.v23376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23376 s i)) at 1.
  unfold R.v23376, N.v23376.
  unfold R.v6, N.v6.
  rewrite ?node_8701.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23377 (s : N.State) (i : N.Inputs) :
  R.v23377 (state s) (inputs i) = Zmod.unsigned (N.v23377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23377 s i)) at 1.
  unfold R.v23377, N.v23377.
  unfold R.v6, N.v6.
  rewrite ?node_8753.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23378 (s : N.State) (i : N.Inputs) :
  R.v23378 (state s) (inputs i) = Zmod.unsigned (N.v23378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23378 s i)) at 1.
  unfold R.v23378, N.v23378.
  rewrite ?node_23375.
  rewrite ?node_23376.
  rewrite ?node_23377.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23379 (s : N.State) (i : N.Inputs) :
  R.v23379 (state s) (inputs i) = Zmod.unsigned (N.v23379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23379 s i)) at 1.
  unfold R.v23379, N.v23379.
  rewrite ?node_23374.
  rewrite ?node_23378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23380 (s : N.State) (i : N.Inputs) :
  R.v23380 (state s) (inputs i) = Zmod.unsigned (N.v23380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23380 s i)) at 1.
  unfold R.v23380, N.v23380.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23381 (s : N.State) (i : N.Inputs) :
  R.v23381 (state s) (inputs i) = Zmod.unsigned (N.v23381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23381 s i)) at 1.
  unfold R.v23381, N.v23381.
  unfold R.v16463, N.v16463.
  rewrite !state_r764_nr_5F764.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r764_nr_5F764 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23382 (s : N.State) (i : N.Inputs) :
  R.v23382 (state s) (inputs i) = Zmod.unsigned (N.v23382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23382 s i)) at 1.
  unfold R.v23382, N.v23382.
  unfold R.v6, N.v6.
  rewrite !state_r763_nr_5F763.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r763_nr_5F763 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23383 (s : N.State) (i : N.Inputs) :
  R.v23383 (state s) (inputs i) = Zmod.unsigned (N.v23383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23383 s i)) at 1.
  unfold R.v23383, N.v23383.
  unfold R.v6, N.v6.
  rewrite !state_r762_nr_5F762.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r762_nr_5F762 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23384 (s : N.State) (i : N.Inputs) :
  R.v23384 (state s) (inputs i) = Zmod.unsigned (N.v23384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23384 s i)) at 1.
  unfold R.v23384, N.v23384.
  rewrite ?node_23382.
  rewrite ?node_23383.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23385 (s : N.State) (i : N.Inputs) :
  R.v23385 (state s) (inputs i) = Zmod.unsigned (N.v23385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23385 s i)) at 1.
  unfold R.v23385, N.v23385.
  unfold R.v16484, N.v16484.
  rewrite ?node_23384.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23386 (s : N.State) (i : N.Inputs) :
  R.v23386 (state s) (inputs i) = Zmod.unsigned (N.v23386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23386 s i)) at 1.
  unfold R.v23386, N.v23386.
  rewrite ?node_23381.
  rewrite ?node_23385.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23387 (s : N.State) (i : N.Inputs) :
  R.v23387 (state s) (inputs i) = Zmod.unsigned (N.v23387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23387 s i)) at 1.
  unfold R.v23387, N.v23387.
  unfold R.v6, N.v6.
  rewrite ?node_23386.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23388 (s : N.State) (i : N.Inputs) :
  R.v23388 (state s) (inputs i) = Zmod.unsigned (N.v23388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23388 s i)) at 1.
  unfold R.v23388, N.v23388.
  rewrite ?node_8565.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23389 (s : N.State) (i : N.Inputs) :
  R.v23389 (state s) (inputs i) = Zmod.unsigned (N.v23389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23389 s i)) at 1.
  unfold R.v23389, N.v23389.
  unfold R.v6, N.v6.
  rewrite ?node_8701.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23390 (s : N.State) (i : N.Inputs) :
  R.v23390 (state s) (inputs i) = Zmod.unsigned (N.v23390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23390 s i)) at 1.
  unfold R.v23390, N.v23390.
  rewrite ?node_23388.
  rewrite ?node_23389.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23391 (s : N.State) (i : N.Inputs) :
  R.v23391 (state s) (inputs i) = Zmod.unsigned (N.v23391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23391 s i)) at 1.
  unfold R.v23391, N.v23391.
  rewrite ?node_23387.
  rewrite ?node_23390.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23392 (s : N.State) (i : N.Inputs) :
  R.v23392 (state s) (inputs i) = Zmod.unsigned (N.v23392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23392 s i)) at 1.
  unfold R.v23392, N.v23392.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23393 (s : N.State) (i : N.Inputs) :
  R.v23393 (state s) (inputs i) = Zmod.unsigned (N.v23393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23393 s i)) at 1.
  unfold R.v23393, N.v23393.
  rewrite ?node_8569.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23394 (s : N.State) (i : N.Inputs) :
  R.v23394 (state s) (inputs i) = Zmod.unsigned (N.v23394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23394 s i)) at 1.
  unfold R.v23394, N.v23394.
  unfold R.v6, N.v6.
  rewrite !state_r765_nr_5F765.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r765_nr_5F765 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23395 (s : N.State) (i : N.Inputs) :
  R.v23395 (state s) (inputs i) = Zmod.unsigned (N.v23395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23395 s i)) at 1.
  unfold R.v23395, N.v23395.
  unfold R.v6, N.v6.
  rewrite ?node_8565.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23396 (s : N.State) (i : N.Inputs) :
  R.v23396 (state s) (inputs i) = Zmod.unsigned (N.v23396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23396 s i)) at 1.
  unfold R.v23396, N.v23396.
  rewrite ?node_23394.
  rewrite ?node_23395.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23397 (s : N.State) (i : N.Inputs) :
  R.v23397 (state s) (inputs i) = Zmod.unsigned (N.v23397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23397 s i)) at 1.
  unfold R.v23397, N.v23397.
  unfold R.v16484, N.v16484.
  rewrite ?node_23396.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23398 (s : N.State) (i : N.Inputs) :
  R.v23398 (state s) (inputs i) = Zmod.unsigned (N.v23398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23398 s i)) at 1.
  unfold R.v23398, N.v23398.
  rewrite ?node_23393.
  rewrite ?node_23397.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23399 (s : N.State) (i : N.Inputs) :
  R.v23399 (state s) (inputs i) = Zmod.unsigned (N.v23399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23399 s i)) at 1.
  unfold R.v23399, N.v23399.
  unfold R.v6, N.v6.
  rewrite ?node_23398.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23400 (s : N.State) (i : N.Inputs) :
  R.v23400 (state s) (inputs i) = Zmod.unsigned (N.v23400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23400 s i)) at 1.
  unfold R.v23400, N.v23400.
  rewrite ?node_8570.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23401 (s : N.State) (i : N.Inputs) :
  R.v23401 (state s) (inputs i) = Zmod.unsigned (N.v23401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23401 s i)) at 1.
  unfold R.v23401, N.v23401.
  unfold R.v6, N.v6.
  rewrite ?node_8753.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23402 (s : N.State) (i : N.Inputs) :
  R.v23402 (state s) (inputs i) = Zmod.unsigned (N.v23402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23402 s i)) at 1.
  unfold R.v23402, N.v23402.
  rewrite ?node_23400.
  rewrite ?node_23401.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23403 (s : N.State) (i : N.Inputs) :
  R.v23403 (state s) (inputs i) = Zmod.unsigned (N.v23403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23403 s i)) at 1.
  unfold R.v23403, N.v23403.
  rewrite ?node_23399.
  rewrite ?node_23402.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23404 (s : N.State) (i : N.Inputs) :
  R.v23404 (state s) (inputs i) = Zmod.unsigned (N.v23404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23404 s i)) at 1.
  unfold R.v23404, N.v23404.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23405 (s : N.State) (i : N.Inputs) :
  R.v23405 (state s) (inputs i) = Zmod.unsigned (N.v23405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23405 s i)) at 1.
  unfold R.v23405, N.v23405.
  rewrite ?node_8577.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23406 (s : N.State) (i : N.Inputs) :
  R.v23406 (state s) (inputs i) = Zmod.unsigned (N.v23406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23406 s i)) at 1.
  unfold R.v23406, N.v23406.
  unfold R.v16463, N.v16463.
  rewrite !state_r769_nr_5F769.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r769_nr_5F769 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23407 (s : N.State) (i : N.Inputs) :
  R.v23407 (state s) (inputs i) = Zmod.unsigned (N.v23407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23407 s i)) at 1.
  unfold R.v23407, N.v23407.
  unfold R.v16463, N.v16463.
  rewrite !state_r768_nr_5F768.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r768_nr_5F768 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23408 (s : N.State) (i : N.Inputs) :
  R.v23408 (state s) (inputs i) = Zmod.unsigned (N.v23408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23408 s i)) at 1.
  unfold R.v23408, N.v23408.
  unfold R.v6, N.v6.
  rewrite !state_r767_nr_5F767.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r767_nr_5F767 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23409 (s : N.State) (i : N.Inputs) :
  R.v23409 (state s) (inputs i) = Zmod.unsigned (N.v23409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23409 s i)) at 1.
  unfold R.v23409, N.v23409.
  unfold R.v6, N.v6.
  rewrite !state_r766_nr_5F766.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r766_nr_5F766 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23410 (s : N.State) (i : N.Inputs) :
  R.v23410 (state s) (inputs i) = Zmod.unsigned (N.v23410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23410 s i)) at 1.
  unfold R.v23410, N.v23410.
  rewrite ?node_23408.
  rewrite ?node_23409.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23411 (s : N.State) (i : N.Inputs) :
  R.v23411 (state s) (inputs i) = Zmod.unsigned (N.v23411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23411 s i)) at 1.
  unfold R.v23411, N.v23411.
  unfold R.v16484, N.v16484.
  rewrite ?node_23410.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23412 (s : N.State) (i : N.Inputs) :
  R.v23412 (state s) (inputs i) = Zmod.unsigned (N.v23412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23412 s i)) at 1.
  unfold R.v23412, N.v23412.
  rewrite ?node_23405.
  rewrite ?node_23406.
  rewrite ?node_23407.
  rewrite ?node_23411.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23413 (s : N.State) (i : N.Inputs) :
  R.v23413 (state s) (inputs i) = Zmod.unsigned (N.v23413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23413 s i)) at 1.
  unfold R.v23413, N.v23413.
  unfold R.v6, N.v6.
  rewrite ?node_23412.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23414 (s : N.State) (i : N.Inputs) :
  R.v23414 (state s) (inputs i) = Zmod.unsigned (N.v23414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23414 s i)) at 1.
  unfold R.v23414, N.v23414.
  rewrite ?node_8578.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23415 (s : N.State) (i : N.Inputs) :
  R.v23415 (state s) (inputs i) = Zmod.unsigned (N.v23415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23415 s i)) at 1.
  unfold R.v23415, N.v23415.
  unfold R.v6, N.v6.
  rewrite ?node_8709.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23416 (s : N.State) (i : N.Inputs) :
  R.v23416 (state s) (inputs i) = Zmod.unsigned (N.v23416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23416 s i)) at 1.
  unfold R.v23416, N.v23416.
  unfold R.v6, N.v6.
  rewrite ?node_8757.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23417 (s : N.State) (i : N.Inputs) :
  R.v23417 (state s) (inputs i) = Zmod.unsigned (N.v23417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23417 s i)) at 1.
  unfold R.v23417, N.v23417.
  rewrite ?node_23414.
  rewrite ?node_23415.
  rewrite ?node_23416.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23418 (s : N.State) (i : N.Inputs) :
  R.v23418 (state s) (inputs i) = Zmod.unsigned (N.v23418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23418 s i)) at 1.
  unfold R.v23418, N.v23418.
  rewrite ?node_23413.
  rewrite ?node_23417.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23419 (s : N.State) (i : N.Inputs) :
  R.v23419 (state s) (inputs i) = Zmod.unsigned (N.v23419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23419 s i)) at 1.
  unfold R.v23419, N.v23419.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23420 (s : N.State) (i : N.Inputs) :
  R.v23420 (state s) (inputs i) = Zmod.unsigned (N.v23420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23420 s i)) at 1.
  unfold R.v23420, N.v23420.
  unfold R.v16463, N.v16463.
  rewrite !state_r768_nr_5F768.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r768_nr_5F768 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23421 (s : N.State) (i : N.Inputs) :
  R.v23421 (state s) (inputs i) = Zmod.unsigned (N.v23421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23421 s i)) at 1.
  unfold R.v23421, N.v23421.
  unfold R.v6, N.v6.
  rewrite !state_r767_nr_5F767.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r767_nr_5F767 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23422 (s : N.State) (i : N.Inputs) :
  R.v23422 (state s) (inputs i) = Zmod.unsigned (N.v23422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23422 s i)) at 1.
  unfold R.v23422, N.v23422.
  unfold R.v6, N.v6.
  rewrite !state_r766_nr_5F766.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r766_nr_5F766 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23423 (s : N.State) (i : N.Inputs) :
  R.v23423 (state s) (inputs i) = Zmod.unsigned (N.v23423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23423 s i)) at 1.
  unfold R.v23423, N.v23423.
  rewrite ?node_23421.
  rewrite ?node_23422.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23424 (s : N.State) (i : N.Inputs) :
  R.v23424 (state s) (inputs i) = Zmod.unsigned (N.v23424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23424 s i)) at 1.
  unfold R.v23424, N.v23424.
  unfold R.v16484, N.v16484.
  rewrite ?node_23423.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23425 (s : N.State) (i : N.Inputs) :
  R.v23425 (state s) (inputs i) = Zmod.unsigned (N.v23425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23425 s i)) at 1.
  unfold R.v23425, N.v23425.
  rewrite ?node_23420.
  rewrite ?node_23424.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23426 (s : N.State) (i : N.Inputs) :
  R.v23426 (state s) (inputs i) = Zmod.unsigned (N.v23426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23426 s i)) at 1.
  unfold R.v23426, N.v23426.
  unfold R.v6, N.v6.
  rewrite ?node_23425.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23427 (s : N.State) (i : N.Inputs) :
  R.v23427 (state s) (inputs i) = Zmod.unsigned (N.v23427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23427 s i)) at 1.
  unfold R.v23427, N.v23427.
  rewrite ?node_8573.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23428 (s : N.State) (i : N.Inputs) :
  R.v23428 (state s) (inputs i) = Zmod.unsigned (N.v23428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23428 s i)) at 1.
  unfold R.v23428, N.v23428.
  unfold R.v6, N.v6.
  rewrite ?node_8709.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23429 (s : N.State) (i : N.Inputs) :
  R.v23429 (state s) (inputs i) = Zmod.unsigned (N.v23429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23429 s i)) at 1.
  unfold R.v23429, N.v23429.
  rewrite ?node_23427.
  rewrite ?node_23428.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23430 (s : N.State) (i : N.Inputs) :
  R.v23430 (state s) (inputs i) = Zmod.unsigned (N.v23430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23430 s i)) at 1.
  unfold R.v23430, N.v23430.
  rewrite ?node_23426.
  rewrite ?node_23429.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23431 (s : N.State) (i : N.Inputs) :
  R.v23431 (state s) (inputs i) = Zmod.unsigned (N.v23431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23431 s i)) at 1.
  unfold R.v23431, N.v23431.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23432 (s : N.State) (i : N.Inputs) :
  R.v23432 (state s) (inputs i) = Zmod.unsigned (N.v23432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23432 s i)) at 1.
  unfold R.v23432, N.v23432.
  rewrite ?node_8577.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23433 (s : N.State) (i : N.Inputs) :
  R.v23433 (state s) (inputs i) = Zmod.unsigned (N.v23433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23433 s i)) at 1.
  unfold R.v23433, N.v23433.
  unfold R.v6, N.v6.
  rewrite !state_r769_nr_5F769.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r769_nr_5F769 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23434 (s : N.State) (i : N.Inputs) :
  R.v23434 (state s) (inputs i) = Zmod.unsigned (N.v23434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23434 s i)) at 1.
  unfold R.v23434, N.v23434.
  unfold R.v6, N.v6.
  rewrite ?node_8573.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23435 (s : N.State) (i : N.Inputs) :
  R.v23435 (state s) (inputs i) = Zmod.unsigned (N.v23435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23435 s i)) at 1.
  unfold R.v23435, N.v23435.
  rewrite ?node_23433.
  rewrite ?node_23434.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23436 (s : N.State) (i : N.Inputs) :
  R.v23436 (state s) (inputs i) = Zmod.unsigned (N.v23436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23436 s i)) at 1.
  unfold R.v23436, N.v23436.
  unfold R.v16484, N.v16484.
  rewrite ?node_23435.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23437 (s : N.State) (i : N.Inputs) :
  R.v23437 (state s) (inputs i) = Zmod.unsigned (N.v23437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23437 s i)) at 1.
  unfold R.v23437, N.v23437.
  rewrite ?node_23432.
  rewrite ?node_23436.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23438 (s : N.State) (i : N.Inputs) :
  R.v23438 (state s) (inputs i) = Zmod.unsigned (N.v23438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23438 s i)) at 1.
  unfold R.v23438, N.v23438.
  unfold R.v6, N.v6.
  rewrite ?node_23437.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23439 (s : N.State) (i : N.Inputs) :
  R.v23439 (state s) (inputs i) = Zmod.unsigned (N.v23439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23439 s i)) at 1.
  unfold R.v23439, N.v23439.
  rewrite ?node_8578.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23440 (s : N.State) (i : N.Inputs) :
  R.v23440 (state s) (inputs i) = Zmod.unsigned (N.v23440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23440 s i)) at 1.
  unfold R.v23440, N.v23440.
  unfold R.v6, N.v6.
  rewrite ?node_8757.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23441 (s : N.State) (i : N.Inputs) :
  R.v23441 (state s) (inputs i) = Zmod.unsigned (N.v23441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23441 s i)) at 1.
  unfold R.v23441, N.v23441.
  rewrite ?node_23439.
  rewrite ?node_23440.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23442 (s : N.State) (i : N.Inputs) :
  R.v23442 (state s) (inputs i) = Zmod.unsigned (N.v23442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23442 s i)) at 1.
  unfold R.v23442, N.v23442.
  rewrite ?node_23438.
  rewrite ?node_23441.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23443 (s : N.State) (i : N.Inputs) :
  R.v23443 (state s) (inputs i) = Zmod.unsigned (N.v23443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23443 s i)) at 1.
  unfold R.v23443, N.v23443.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23444 (s : N.State) (i : N.Inputs) :
  R.v23444 (state s) (inputs i) = Zmod.unsigned (N.v23444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23444 s i)) at 1.
  unfold R.v23444, N.v23444.
  rewrite ?node_8589.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23445 (s : N.State) (i : N.Inputs) :
  R.v23445 (state s) (inputs i) = Zmod.unsigned (N.v23445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23445 s i)) at 1.
  unfold R.v23445, N.v23445.
  unfold R.v16463, N.v16463.
  rewrite !state_r773_nr_5F773.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r773_nr_5F773 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23446 (s : N.State) (i : N.Inputs) :
  R.v23446 (state s) (inputs i) = Zmod.unsigned (N.v23446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23446 s i)) at 1.
  unfold R.v23446, N.v23446.
  unfold R.v16463, N.v16463.
  rewrite !state_r772_nr_5F772.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r772_nr_5F772 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23447 (s : N.State) (i : N.Inputs) :
  R.v23447 (state s) (inputs i) = Zmod.unsigned (N.v23447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23447 s i)) at 1.
  unfold R.v23447, N.v23447.
  unfold R.v6, N.v6.
  rewrite !state_r771_nr_5F771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r771_nr_5F771 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23448 (s : N.State) (i : N.Inputs) :
  R.v23448 (state s) (inputs i) = Zmod.unsigned (N.v23448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23448 s i)) at 1.
  unfold R.v23448, N.v23448.
  unfold R.v6, N.v6.
  rewrite !state_r770_nr_5F770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r770_nr_5F770 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23449 (s : N.State) (i : N.Inputs) :
  R.v23449 (state s) (inputs i) = Zmod.unsigned (N.v23449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23449 s i)) at 1.
  unfold R.v23449, N.v23449.
  rewrite ?node_23447.
  rewrite ?node_23448.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23450 (s : N.State) (i : N.Inputs) :
  R.v23450 (state s) (inputs i) = Zmod.unsigned (N.v23450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23450 s i)) at 1.
  unfold R.v23450, N.v23450.
  unfold R.v16484, N.v16484.
  rewrite ?node_23449.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23451 (s : N.State) (i : N.Inputs) :
  R.v23451 (state s) (inputs i) = Zmod.unsigned (N.v23451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23451 s i)) at 1.
  unfold R.v23451, N.v23451.
  rewrite ?node_23444.
  rewrite ?node_23445.
  rewrite ?node_23446.
  rewrite ?node_23450.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23452 (s : N.State) (i : N.Inputs) :
  R.v23452 (state s) (inputs i) = Zmod.unsigned (N.v23452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23452 s i)) at 1.
  unfold R.v23452, N.v23452.
  unfold R.v6, N.v6.
  rewrite ?node_23451.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23453 (s : N.State) (i : N.Inputs) :
  R.v23453 (state s) (inputs i) = Zmod.unsigned (N.v23453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23453 s i)) at 1.
  unfold R.v23453, N.v23453.
  rewrite ?node_8590.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23454 (s : N.State) (i : N.Inputs) :
  R.v23454 (state s) (inputs i) = Zmod.unsigned (N.v23454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23454 s i)) at 1.
  unfold R.v23454, N.v23454.
  unfold R.v6, N.v6.
  rewrite ?node_8721.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23455 (s : N.State) (i : N.Inputs) :
  R.v23455 (state s) (inputs i) = Zmod.unsigned (N.v23455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23455 s i)) at 1.
  unfold R.v23455, N.v23455.
  unfold R.v6, N.v6.
  rewrite ?node_8761.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23456 (s : N.State) (i : N.Inputs) :
  R.v23456 (state s) (inputs i) = Zmod.unsigned (N.v23456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23456 s i)) at 1.
  unfold R.v23456, N.v23456.
  rewrite ?node_23453.
  rewrite ?node_23454.
  rewrite ?node_23455.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23457 (s : N.State) (i : N.Inputs) :
  R.v23457 (state s) (inputs i) = Zmod.unsigned (N.v23457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23457 s i)) at 1.
  unfold R.v23457, N.v23457.
  rewrite ?node_23452.
  rewrite ?node_23456.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23458 (s : N.State) (i : N.Inputs) :
  R.v23458 (state s) (inputs i) = Zmod.unsigned (N.v23458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23458 s i)) at 1.
  unfold R.v23458, N.v23458.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23459 (s : N.State) (i : N.Inputs) :
  R.v23459 (state s) (inputs i) = Zmod.unsigned (N.v23459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23459 s i)) at 1.
  unfold R.v23459, N.v23459.
  unfold R.v16463, N.v16463.
  rewrite !state_r772_nr_5F772.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r772_nr_5F772 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23460 (s : N.State) (i : N.Inputs) :
  R.v23460 (state s) (inputs i) = Zmod.unsigned (N.v23460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23460 s i)) at 1.
  unfold R.v23460, N.v23460.
  unfold R.v6, N.v6.
  rewrite !state_r771_nr_5F771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r771_nr_5F771 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23461 (s : N.State) (i : N.Inputs) :
  R.v23461 (state s) (inputs i) = Zmod.unsigned (N.v23461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23461 s i)) at 1.
  unfold R.v23461, N.v23461.
  unfold R.v6, N.v6.
  rewrite !state_r770_nr_5F770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r770_nr_5F770 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23462 (s : N.State) (i : N.Inputs) :
  R.v23462 (state s) (inputs i) = Zmod.unsigned (N.v23462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23462 s i)) at 1.
  unfold R.v23462, N.v23462.
  rewrite ?node_23460.
  rewrite ?node_23461.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23463 (s : N.State) (i : N.Inputs) :
  R.v23463 (state s) (inputs i) = Zmod.unsigned (N.v23463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23463 s i)) at 1.
  unfold R.v23463, N.v23463.
  unfold R.v16484, N.v16484.
  rewrite ?node_23462.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23464 (s : N.State) (i : N.Inputs) :
  R.v23464 (state s) (inputs i) = Zmod.unsigned (N.v23464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23464 s i)) at 1.
  unfold R.v23464, N.v23464.
  rewrite ?node_23459.
  rewrite ?node_23463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23465 (s : N.State) (i : N.Inputs) :
  R.v23465 (state s) (inputs i) = Zmod.unsigned (N.v23465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23465 s i)) at 1.
  unfold R.v23465, N.v23465.
  unfold R.v6, N.v6.
  rewrite ?node_23464.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23466 (s : N.State) (i : N.Inputs) :
  R.v23466 (state s) (inputs i) = Zmod.unsigned (N.v23466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23466 s i)) at 1.
  unfold R.v23466, N.v23466.
  rewrite ?node_8585.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23467 (s : N.State) (i : N.Inputs) :
  R.v23467 (state s) (inputs i) = Zmod.unsigned (N.v23467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23467 s i)) at 1.
  unfold R.v23467, N.v23467.
  unfold R.v6, N.v6.
  rewrite ?node_8721.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23468 (s : N.State) (i : N.Inputs) :
  R.v23468 (state s) (inputs i) = Zmod.unsigned (N.v23468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23468 s i)) at 1.
  unfold R.v23468, N.v23468.
  rewrite ?node_23466.
  rewrite ?node_23467.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23469 (s : N.State) (i : N.Inputs) :
  R.v23469 (state s) (inputs i) = Zmod.unsigned (N.v23469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23469 s i)) at 1.
  unfold R.v23469, N.v23469.
  rewrite ?node_23465.
  rewrite ?node_23468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23470 (s : N.State) (i : N.Inputs) :
  R.v23470 (state s) (inputs i) = Zmod.unsigned (N.v23470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23470 s i)) at 1.
  unfold R.v23470, N.v23470.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23471 (s : N.State) (i : N.Inputs) :
  R.v23471 (state s) (inputs i) = Zmod.unsigned (N.v23471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23471 s i)) at 1.
  unfold R.v23471, N.v23471.
  rewrite ?node_8589.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23472 (s : N.State) (i : N.Inputs) :
  R.v23472 (state s) (inputs i) = Zmod.unsigned (N.v23472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23472 s i)) at 1.
  unfold R.v23472, N.v23472.
  unfold R.v6, N.v6.
  rewrite !state_r773_nr_5F773.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r773_nr_5F773 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23473 (s : N.State) (i : N.Inputs) :
  R.v23473 (state s) (inputs i) = Zmod.unsigned (N.v23473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23473 s i)) at 1.
  unfold R.v23473, N.v23473.
  unfold R.v6, N.v6.
  rewrite ?node_8585.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23474 (s : N.State) (i : N.Inputs) :
  R.v23474 (state s) (inputs i) = Zmod.unsigned (N.v23474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23474 s i)) at 1.
  unfold R.v23474, N.v23474.
  rewrite ?node_23472.
  rewrite ?node_23473.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23475 (s : N.State) (i : N.Inputs) :
  R.v23475 (state s) (inputs i) = Zmod.unsigned (N.v23475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23475 s i)) at 1.
  unfold R.v23475, N.v23475.
  unfold R.v16484, N.v16484.
  rewrite ?node_23474.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23476 (s : N.State) (i : N.Inputs) :
  R.v23476 (state s) (inputs i) = Zmod.unsigned (N.v23476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23476 s i)) at 1.
  unfold R.v23476, N.v23476.
  rewrite ?node_23471.
  rewrite ?node_23475.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23477 (s : N.State) (i : N.Inputs) :
  R.v23477 (state s) (inputs i) = Zmod.unsigned (N.v23477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23477 s i)) at 1.
  unfold R.v23477, N.v23477.
  unfold R.v6, N.v6.
  rewrite ?node_23476.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23478 (s : N.State) (i : N.Inputs) :
  R.v23478 (state s) (inputs i) = Zmod.unsigned (N.v23478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23478 s i)) at 1.
  unfold R.v23478, N.v23478.
  rewrite ?node_8590.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23479 (s : N.State) (i : N.Inputs) :
  R.v23479 (state s) (inputs i) = Zmod.unsigned (N.v23479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23479 s i)) at 1.
  unfold R.v23479, N.v23479.
  unfold R.v6, N.v6.
  rewrite ?node_8761.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23480 (s : N.State) (i : N.Inputs) :
  R.v23480 (state s) (inputs i) = Zmod.unsigned (N.v23480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23480 s i)) at 1.
  unfold R.v23480, N.v23480.
  rewrite ?node_23478.
  rewrite ?node_23479.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23481 (s : N.State) (i : N.Inputs) :
  R.v23481 (state s) (inputs i) = Zmod.unsigned (N.v23481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23481 s i)) at 1.
  unfold R.v23481, N.v23481.
  rewrite ?node_23477.
  rewrite ?node_23480.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23482 (s : N.State) (i : N.Inputs) :
  R.v23482 (state s) (inputs i) = Zmod.unsigned (N.v23482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23482 s i)) at 1.
  unfold R.v23482, N.v23482.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23483 (s : N.State) (i : N.Inputs) :
  R.v23483 (state s) (inputs i) = Zmod.unsigned (N.v23483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23483 s i)) at 1.
  unfold R.v23483, N.v23483.
  rewrite ?node_8596.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23484 (s : N.State) (i : N.Inputs) :
  R.v23484 (state s) (inputs i) = Zmod.unsigned (N.v23484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23484 s i)) at 1.
  unfold R.v23484, N.v23484.
  unfold R.v16463, N.v16463.
  rewrite !state_r777_nr_5F777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r777_nr_5F777 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23485 (s : N.State) (i : N.Inputs) :
  R.v23485 (state s) (inputs i) = Zmod.unsigned (N.v23485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23485 s i)) at 1.
  unfold R.v23485, N.v23485.
  unfold R.v16463, N.v16463.
  rewrite !state_r776_nr_5F776.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r776_nr_5F776 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23486 (s : N.State) (i : N.Inputs) :
  R.v23486 (state s) (inputs i) = Zmod.unsigned (N.v23486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23486 s i)) at 1.
  unfold R.v23486, N.v23486.
  unfold R.v6, N.v6.
  rewrite !state_r775_nr_5F775.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r775_nr_5F775 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23487 (s : N.State) (i : N.Inputs) :
  R.v23487 (state s) (inputs i) = Zmod.unsigned (N.v23487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23487 s i)) at 1.
  unfold R.v23487, N.v23487.
  unfold R.v6, N.v6.
  rewrite !state_r774_nr_5F774.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r774_nr_5F774 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23488 (s : N.State) (i : N.Inputs) :
  R.v23488 (state s) (inputs i) = Zmod.unsigned (N.v23488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23488 s i)) at 1.
  unfold R.v23488, N.v23488.
  rewrite ?node_23486.
  rewrite ?node_23487.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23489 (s : N.State) (i : N.Inputs) :
  R.v23489 (state s) (inputs i) = Zmod.unsigned (N.v23489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23489 s i)) at 1.
  unfold R.v23489, N.v23489.
  unfold R.v16484, N.v16484.
  rewrite ?node_23488.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23490 (s : N.State) (i : N.Inputs) :
  R.v23490 (state s) (inputs i) = Zmod.unsigned (N.v23490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23490 s i)) at 1.
  unfold R.v23490, N.v23490.
  rewrite ?node_23483.
  rewrite ?node_23484.
  rewrite ?node_23485.
  rewrite ?node_23489.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23491 (s : N.State) (i : N.Inputs) :
  R.v23491 (state s) (inputs i) = Zmod.unsigned (N.v23491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23491 s i)) at 1.
  unfold R.v23491, N.v23491.
  unfold R.v6, N.v6.
  rewrite ?node_23490.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23492 (s : N.State) (i : N.Inputs) :
  R.v23492 (state s) (inputs i) = Zmod.unsigned (N.v23492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23492 s i)) at 1.
  unfold R.v23492, N.v23492.
  rewrite ?node_8597.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23493 (s : N.State) (i : N.Inputs) :
  R.v23493 (state s) (inputs i) = Zmod.unsigned (N.v23493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23493 s i)) at 1.
  unfold R.v23493, N.v23493.
  unfold R.v6, N.v6.
  rewrite ?node_8728.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23494 (s : N.State) (i : N.Inputs) :
  R.v23494 (state s) (inputs i) = Zmod.unsigned (N.v23494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23494 s i)) at 1.
  unfold R.v23494, N.v23494.
  unfold R.v6, N.v6.
  rewrite ?node_8770.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23495 (s : N.State) (i : N.Inputs) :
  R.v23495 (state s) (inputs i) = Zmod.unsigned (N.v23495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23495 s i)) at 1.
  unfold R.v23495, N.v23495.
  rewrite ?node_23492.
  rewrite ?node_23493.
  rewrite ?node_23494.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23496 (s : N.State) (i : N.Inputs) :
  R.v23496 (state s) (inputs i) = Zmod.unsigned (N.v23496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23496 s i)) at 1.
  unfold R.v23496, N.v23496.
  rewrite ?node_23491.
  rewrite ?node_23495.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23497 (s : N.State) (i : N.Inputs) :
  R.v23497 (state s) (inputs i) = Zmod.unsigned (N.v23497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23497 s i)) at 1.
  unfold R.v23497, N.v23497.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23498 (s : N.State) (i : N.Inputs) :
  R.v23498 (state s) (inputs i) = Zmod.unsigned (N.v23498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23498 s i)) at 1.
  unfold R.v23498, N.v23498.
  unfold R.v16463, N.v16463.
  rewrite !state_r776_nr_5F776.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r776_nr_5F776 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23499 (s : N.State) (i : N.Inputs) :
  R.v23499 (state s) (inputs i) = Zmod.unsigned (N.v23499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23499 s i)) at 1.
  unfold R.v23499, N.v23499.
  unfold R.v6, N.v6.
  rewrite !state_r775_nr_5F775.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r775_nr_5F775 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23500 (s : N.State) (i : N.Inputs) :
  R.v23500 (state s) (inputs i) = Zmod.unsigned (N.v23500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23500 s i)) at 1.
  unfold R.v23500, N.v23500.
  unfold R.v6, N.v6.
  rewrite !state_r774_nr_5F774.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r774_nr_5F774 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23501 (s : N.State) (i : N.Inputs) :
  R.v23501 (state s) (inputs i) = Zmod.unsigned (N.v23501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23501 s i)) at 1.
  unfold R.v23501, N.v23501.
  rewrite ?node_23499.
  rewrite ?node_23500.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23502 (s : N.State) (i : N.Inputs) :
  R.v23502 (state s) (inputs i) = Zmod.unsigned (N.v23502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23502 s i)) at 1.
  unfold R.v23502, N.v23502.
  unfold R.v16484, N.v16484.
  rewrite ?node_23501.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23503 (s : N.State) (i : N.Inputs) :
  R.v23503 (state s) (inputs i) = Zmod.unsigned (N.v23503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23503 s i)) at 1.
  unfold R.v23503, N.v23503.
  rewrite ?node_23498.
  rewrite ?node_23502.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23504 (s : N.State) (i : N.Inputs) :
  R.v23504 (state s) (inputs i) = Zmod.unsigned (N.v23504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23504 s i)) at 1.
  unfold R.v23504, N.v23504.
  unfold R.v6, N.v6.
  rewrite ?node_23503.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23505 (s : N.State) (i : N.Inputs) :
  R.v23505 (state s) (inputs i) = Zmod.unsigned (N.v23505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23505 s i)) at 1.
  unfold R.v23505, N.v23505.
  rewrite ?node_8592.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23506 (s : N.State) (i : N.Inputs) :
  R.v23506 (state s) (inputs i) = Zmod.unsigned (N.v23506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23506 s i)) at 1.
  unfold R.v23506, N.v23506.
  unfold R.v6, N.v6.
  rewrite ?node_8728.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23507 (s : N.State) (i : N.Inputs) :
  R.v23507 (state s) (inputs i) = Zmod.unsigned (N.v23507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23507 s i)) at 1.
  unfold R.v23507, N.v23507.
  rewrite ?node_23505.
  rewrite ?node_23506.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23508 (s : N.State) (i : N.Inputs) :
  R.v23508 (state s) (inputs i) = Zmod.unsigned (N.v23508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23508 s i)) at 1.
  unfold R.v23508, N.v23508.
  rewrite ?node_23504.
  rewrite ?node_23507.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23509 (s : N.State) (i : N.Inputs) :
  R.v23509 (state s) (inputs i) = Zmod.unsigned (N.v23509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23509 s i)) at 1.
  unfold R.v23509, N.v23509.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23510 (s : N.State) (i : N.Inputs) :
  R.v23510 (state s) (inputs i) = Zmod.unsigned (N.v23510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23510 s i)) at 1.
  unfold R.v23510, N.v23510.
  rewrite ?node_8596.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23511 (s : N.State) (i : N.Inputs) :
  R.v23511 (state s) (inputs i) = Zmod.unsigned (N.v23511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23511 s i)) at 1.
  unfold R.v23511, N.v23511.
  unfold R.v6, N.v6.
  rewrite !state_r777_nr_5F777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r777_nr_5F777 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23512 (s : N.State) (i : N.Inputs) :
  R.v23512 (state s) (inputs i) = Zmod.unsigned (N.v23512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23512 s i)) at 1.
  unfold R.v23512, N.v23512.
  unfold R.v6, N.v6.
  rewrite ?node_8592.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23513 (s : N.State) (i : N.Inputs) :
  R.v23513 (state s) (inputs i) = Zmod.unsigned (N.v23513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23513 s i)) at 1.
  unfold R.v23513, N.v23513.
  rewrite ?node_23511.
  rewrite ?node_23512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23514 (s : N.State) (i : N.Inputs) :
  R.v23514 (state s) (inputs i) = Zmod.unsigned (N.v23514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23514 s i)) at 1.
  unfold R.v23514, N.v23514.
  unfold R.v16484, N.v16484.
  rewrite ?node_23513.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23515 (s : N.State) (i : N.Inputs) :
  R.v23515 (state s) (inputs i) = Zmod.unsigned (N.v23515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23515 s i)) at 1.
  unfold R.v23515, N.v23515.
  rewrite ?node_23510.
  rewrite ?node_23514.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23516 (s : N.State) (i : N.Inputs) :
  R.v23516 (state s) (inputs i) = Zmod.unsigned (N.v23516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23516 s i)) at 1.
  unfold R.v23516, N.v23516.
  unfold R.v6, N.v6.
  rewrite ?node_23515.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23517 (s : N.State) (i : N.Inputs) :
  R.v23517 (state s) (inputs i) = Zmod.unsigned (N.v23517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23517 s i)) at 1.
  unfold R.v23517, N.v23517.
  rewrite ?node_8597.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23518 (s : N.State) (i : N.Inputs) :
  R.v23518 (state s) (inputs i) = Zmod.unsigned (N.v23518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23518 s i)) at 1.
  unfold R.v23518, N.v23518.
  unfold R.v6, N.v6.
  rewrite ?node_8770.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23519 (s : N.State) (i : N.Inputs) :
  R.v23519 (state s) (inputs i) = Zmod.unsigned (N.v23519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23519 s i)) at 1.
  unfold R.v23519, N.v23519.
  rewrite ?node_23517.
  rewrite ?node_23518.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23520 (s : N.State) (i : N.Inputs) :
  R.v23520 (state s) (inputs i) = Zmod.unsigned (N.v23520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23520 s i)) at 1.
  unfold R.v23520, N.v23520.
  rewrite ?node_23516.
  rewrite ?node_23519.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23521 (s : N.State) (i : N.Inputs) :
  R.v23521 (state s) (inputs i) = Zmod.unsigned (N.v23521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23521 s i)) at 1.
  unfold R.v23521, N.v23521.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23522 (s : N.State) (i : N.Inputs) :
  R.v23522 (state s) (inputs i) = Zmod.unsigned (N.v23522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23522 s i)) at 1.
  unfold R.v23522, N.v23522.
  unfold R.v16463, N.v16463.
  rewrite !state_r781_nr_5F781.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r781_nr_5F781 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23523 (s : N.State) (i : N.Inputs) :
  R.v23523 (state s) (inputs i) = Zmod.unsigned (N.v23523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23523 s i)) at 1.
  unfold R.v23523, N.v23523.
  unfold R.v16463, N.v16463.
  rewrite !state_r780_nr_5F780.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r780_nr_5F780 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23524 (s : N.State) (i : N.Inputs) :
  R.v23524 (state s) (inputs i) = Zmod.unsigned (N.v23524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23524 s i)) at 1.
  unfold R.v23524, N.v23524.
  unfold R.v6, N.v6.
  rewrite !state_r779_nr_5F779.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r779_nr_5F779 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23525 (s : N.State) (i : N.Inputs) :
  R.v23525 (state s) (inputs i) = Zmod.unsigned (N.v23525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23525 s i)) at 1.
  unfold R.v23525, N.v23525.
  unfold R.v6, N.v6.
  rewrite !state_r778_nr_5F778.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r778_nr_5F778 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23526 (s : N.State) (i : N.Inputs) :
  R.v23526 (state s) (inputs i) = Zmod.unsigned (N.v23526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23526 s i)) at 1.
  unfold R.v23526, N.v23526.
  rewrite ?node_23524.
  rewrite ?node_23525.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23527 (s : N.State) (i : N.Inputs) :
  R.v23527 (state s) (inputs i) = Zmod.unsigned (N.v23527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23527 s i)) at 1.
  unfold R.v23527, N.v23527.
  unfold R.v16484, N.v16484.
  rewrite ?node_23526.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23528 (s : N.State) (i : N.Inputs) :
  R.v23528 (state s) (inputs i) = Zmod.unsigned (N.v23528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23528 s i)) at 1.
  unfold R.v23528, N.v23528.
  rewrite ?node_23522.
  rewrite ?node_23523.
  rewrite ?node_23527.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23529 (s : N.State) (i : N.Inputs) :
  R.v23529 (state s) (inputs i) = Zmod.unsigned (N.v23529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23529 s i)) at 1.
  unfold R.v23529, N.v23529.
  unfold R.v6, N.v6.
  rewrite ?node_23528.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23530 (s : N.State) (i : N.Inputs) :
  R.v23530 (state s) (inputs i) = Zmod.unsigned (N.v23530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23530 s i)) at 1.
  unfold R.v23530, N.v23530.
  rewrite ?node_8601.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23531 (s : N.State) (i : N.Inputs) :
  R.v23531 (state s) (inputs i) = Zmod.unsigned (N.v23531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23531 s i)) at 1.
  unfold R.v23531, N.v23531.
  unfold R.v6, N.v6.
  rewrite ?node_8736.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23532 (s : N.State) (i : N.Inputs) :
  R.v23532 (state s) (inputs i) = Zmod.unsigned (N.v23532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23532 s i)) at 1.
  unfold R.v23532, N.v23532.
  unfold R.v6, N.v6.
  rewrite ?node_8771.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23533 (s : N.State) (i : N.Inputs) :
  R.v23533 (state s) (inputs i) = Zmod.unsigned (N.v23533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23533 s i)) at 1.
  unfold R.v23533, N.v23533.
  rewrite ?node_23530.
  rewrite ?node_23531.
  rewrite ?node_23532.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23534 (s : N.State) (i : N.Inputs) :
  R.v23534 (state s) (inputs i) = Zmod.unsigned (N.v23534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23534 s i)) at 1.
  unfold R.v23534, N.v23534.
  rewrite ?node_23529.
  rewrite ?node_23533.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23535 (s : N.State) (i : N.Inputs) :
  R.v23535 (state s) (inputs i) = Zmod.unsigned (N.v23535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23535 s i)) at 1.
  unfold R.v23535, N.v23535.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23536 (s : N.State) (i : N.Inputs) :
  R.v23536 (state s) (inputs i) = Zmod.unsigned (N.v23536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23536 s i)) at 1.
  unfold R.v23536, N.v23536.
  unfold R.v16463, N.v16463.
  rewrite !state_r780_nr_5F780.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r780_nr_5F780 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23537 (s : N.State) (i : N.Inputs) :
  R.v23537 (state s) (inputs i) = Zmod.unsigned (N.v23537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23537 s i)) at 1.
  unfold R.v23537, N.v23537.
  unfold R.v6, N.v6.
  rewrite !state_r779_nr_5F779.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r779_nr_5F779 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23538 (s : N.State) (i : N.Inputs) :
  R.v23538 (state s) (inputs i) = Zmod.unsigned (N.v23538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23538 s i)) at 1.
  unfold R.v23538, N.v23538.
  unfold R.v6, N.v6.
  rewrite !state_r778_nr_5F778.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r778_nr_5F778 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23539 (s : N.State) (i : N.Inputs) :
  R.v23539 (state s) (inputs i) = Zmod.unsigned (N.v23539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23539 s i)) at 1.
  unfold R.v23539, N.v23539.
  rewrite ?node_23537.
  rewrite ?node_23538.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23540 (s : N.State) (i : N.Inputs) :
  R.v23540 (state s) (inputs i) = Zmod.unsigned (N.v23540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23540 s i)) at 1.
  unfold R.v23540, N.v23540.
  unfold R.v16484, N.v16484.
  rewrite ?node_23539.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23541 (s : N.State) (i : N.Inputs) :
  R.v23541 (state s) (inputs i) = Zmod.unsigned (N.v23541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23541 s i)) at 1.
  unfold R.v23541, N.v23541.
  rewrite ?node_23536.
  rewrite ?node_23540.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23542 (s : N.State) (i : N.Inputs) :
  R.v23542 (state s) (inputs i) = Zmod.unsigned (N.v23542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23542 s i)) at 1.
  unfold R.v23542, N.v23542.
  unfold R.v6, N.v6.
  rewrite ?node_23541.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23543 (s : N.State) (i : N.Inputs) :
  R.v23543 (state s) (inputs i) = Zmod.unsigned (N.v23543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23543 s i)) at 1.
  unfold R.v23543, N.v23543.
  rewrite ?node_8600.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23544 (s : N.State) (i : N.Inputs) :
  R.v23544 (state s) (inputs i) = Zmod.unsigned (N.v23544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23544 s i)) at 1.
  unfold R.v23544, N.v23544.
  unfold R.v6, N.v6.
  rewrite ?node_8736.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23545 (s : N.State) (i : N.Inputs) :
  R.v23545 (state s) (inputs i) = Zmod.unsigned (N.v23545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23545 s i)) at 1.
  unfold R.v23545, N.v23545.
  rewrite ?node_23543.
  rewrite ?node_23544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23546 (s : N.State) (i : N.Inputs) :
  R.v23546 (state s) (inputs i) = Zmod.unsigned (N.v23546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23546 s i)) at 1.
  unfold R.v23546, N.v23546.
  rewrite ?node_23542.
  rewrite ?node_23545.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23547 (s : N.State) (i : N.Inputs) :
  R.v23547 (state s) (inputs i) = Zmod.unsigned (N.v23547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23547 s i)) at 1.
  unfold R.v23547, N.v23547.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23548 (s : N.State) (i : N.Inputs) :
  R.v23548 (state s) (inputs i) = Zmod.unsigned (N.v23548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23548 s i)) at 1.
  unfold R.v23548, N.v23548.
  unfold R.v6, N.v6.
  rewrite !state_r781_nr_5F781.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r781_nr_5F781 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23549 (s : N.State) (i : N.Inputs) :
  R.v23549 (state s) (inputs i) = Zmod.unsigned (N.v23549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23549 s i)) at 1.
  unfold R.v23549, N.v23549.
  unfold R.v6, N.v6.
  rewrite ?node_8600.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23550 (s : N.State) (i : N.Inputs) :
  R.v23550 (state s) (inputs i) = Zmod.unsigned (N.v23550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23550 s i)) at 1.
  unfold R.v23550, N.v23550.
  rewrite ?node_23548.
  rewrite ?node_23549.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23551 (s : N.State) (i : N.Inputs) :
  R.v23551 (state s) (inputs i) = Zmod.unsigned (N.v23551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23551 s i)) at 1.
  unfold R.v23551, N.v23551.
  unfold R.v16463, N.v16463.
  rewrite ?node_23550.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23552 (s : N.State) (i : N.Inputs) :
  R.v23552 (state s) (inputs i) = Zmod.unsigned (N.v23552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23552 s i)) at 1.
  unfold R.v23552, N.v23552.
  rewrite ?node_8601.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23553 (s : N.State) (i : N.Inputs) :
  R.v23553 (state s) (inputs i) = Zmod.unsigned (N.v23553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23553 s i)) at 1.
  unfold R.v23553, N.v23553.
  unfold R.v6, N.v6.
  rewrite ?node_8771.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23554 (s : N.State) (i : N.Inputs) :
  R.v23554 (state s) (inputs i) = Zmod.unsigned (N.v23554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23554 s i)) at 1.
  unfold R.v23554, N.v23554.
  rewrite ?node_23552.
  rewrite ?node_23553.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23555 (s : N.State) (i : N.Inputs) :
  R.v23555 (state s) (inputs i) = Zmod.unsigned (N.v23555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23555 s i)) at 1.
  unfold R.v23555, N.v23555.
  rewrite ?node_23551.
  rewrite ?node_23554.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23556 (s : N.State) (i : N.Inputs) :
  R.v23556 (state s) (inputs i) = Zmod.unsigned (N.v23556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23556 s i)) at 1.
  unfold R.v23556, N.v23556.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23557 (s : N.State) (i : N.Inputs) :
  R.v23557 (state s) (inputs i) = Zmod.unsigned (N.v23557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23557 s i)) at 1.
  unfold R.v23557, N.v23557.
  rewrite ?node_8686.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23558 (s : N.State) (i : N.Inputs) :
  R.v23558 (state s) (inputs i) = Zmod.unsigned (N.v23558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23558 s i)) at 1.
  unfold R.v23558, N.v23558.
  unfold R.v16463, N.v16463.
  rewrite !state_r785_nr_5F785.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r785_nr_5F785 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23559 (s : N.State) (i : N.Inputs) :
  R.v23559 (state s) (inputs i) = Zmod.unsigned (N.v23559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23559 s i)) at 1.
  unfold R.v23559, N.v23559.
  unfold R.v16463, N.v16463.
  rewrite !state_r784_nr_5F784.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r784_nr_5F784 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23560 (s : N.State) (i : N.Inputs) :
  R.v23560 (state s) (inputs i) = Zmod.unsigned (N.v23560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23560 s i)) at 1.
  unfold R.v23560, N.v23560.
  unfold R.v6, N.v6.
  rewrite !state_r783_nr_5F783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r783_nr_5F783 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23561 (s : N.State) (i : N.Inputs) :
  R.v23561 (state s) (inputs i) = Zmod.unsigned (N.v23561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23561 s i)) at 1.
  unfold R.v23561, N.v23561.
  unfold R.v6, N.v6.
  rewrite !state_r782_nr_5F782.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r782_nr_5F782 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23562 (s : N.State) (i : N.Inputs) :
  R.v23562 (state s) (inputs i) = Zmod.unsigned (N.v23562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23562 s i)) at 1.
  unfold R.v23562, N.v23562.
  rewrite ?node_23560.
  rewrite ?node_23561.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23563 (s : N.State) (i : N.Inputs) :
  R.v23563 (state s) (inputs i) = Zmod.unsigned (N.v23563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23563 s i)) at 1.
  unfold R.v23563, N.v23563.
  unfold R.v16484, N.v16484.
  rewrite ?node_23562.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23564 (s : N.State) (i : N.Inputs) :
  R.v23564 (state s) (inputs i) = Zmod.unsigned (N.v23564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23564 s i)) at 1.
  unfold R.v23564, N.v23564.
  rewrite ?node_23557.
  rewrite ?node_23558.
  rewrite ?node_23559.
  rewrite ?node_23563.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23565 (s : N.State) (i : N.Inputs) :
  R.v23565 (state s) (inputs i) = Zmod.unsigned (N.v23565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23565 s i)) at 1.
  unfold R.v23565, N.v23565.
  unfold R.v6, N.v6.
  rewrite ?node_23564.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23566 (s : N.State) (i : N.Inputs) :
  R.v23566 (state s) (inputs i) = Zmod.unsigned (N.v23566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23566 s i)) at 1.
  unfold R.v23566, N.v23566.
  rewrite ?node_8687.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23567 (s : N.State) (i : N.Inputs) :
  R.v23567 (state s) (inputs i) = Zmod.unsigned (N.v23567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23567 s i)) at 1.
  unfold R.v23567, N.v23567.
  unfold R.v6, N.v6.
  rewrite ?node_8820.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23568 (s : N.State) (i : N.Inputs) :
  R.v23568 (state s) (inputs i) = Zmod.unsigned (N.v23568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23568 s i)) at 1.
  unfold R.v23568, N.v23568.
  unfold R.v6, N.v6.
  rewrite ?node_8881.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23569 (s : N.State) (i : N.Inputs) :
  R.v23569 (state s) (inputs i) = Zmod.unsigned (N.v23569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23569 s i)) at 1.
  unfold R.v23569, N.v23569.
  rewrite ?node_23566.
  rewrite ?node_23567.
  rewrite ?node_23568.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23570 (s : N.State) (i : N.Inputs) :
  R.v23570 (state s) (inputs i) = Zmod.unsigned (N.v23570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23570 s i)) at 1.
  unfold R.v23570, N.v23570.
  rewrite ?node_23565.
  rewrite ?node_23569.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23571 (s : N.State) (i : N.Inputs) :
  R.v23571 (state s) (inputs i) = Zmod.unsigned (N.v23571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23571 s i)) at 1.
  unfold R.v23571, N.v23571.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23572 (s : N.State) (i : N.Inputs) :
  R.v23572 (state s) (inputs i) = Zmod.unsigned (N.v23572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23572 s i)) at 1.
  unfold R.v23572, N.v23572.
  unfold R.v16463, N.v16463.
  rewrite !state_r784_nr_5F784.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r784_nr_5F784 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23573 (s : N.State) (i : N.Inputs) :
  R.v23573 (state s) (inputs i) = Zmod.unsigned (N.v23573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23573 s i)) at 1.
  unfold R.v23573, N.v23573.
  unfold R.v6, N.v6.
  rewrite !state_r783_nr_5F783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r783_nr_5F783 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23574 (s : N.State) (i : N.Inputs) :
  R.v23574 (state s) (inputs i) = Zmod.unsigned (N.v23574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23574 s i)) at 1.
  unfold R.v23574, N.v23574.
  unfold R.v6, N.v6.
  rewrite !state_r782_nr_5F782.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r782_nr_5F782 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23575 (s : N.State) (i : N.Inputs) :
  R.v23575 (state s) (inputs i) = Zmod.unsigned (N.v23575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23575 s i)) at 1.
  unfold R.v23575, N.v23575.
  rewrite ?node_23573.
  rewrite ?node_23574.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23576 (s : N.State) (i : N.Inputs) :
  R.v23576 (state s) (inputs i) = Zmod.unsigned (N.v23576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23576 s i)) at 1.
  unfold R.v23576, N.v23576.
  unfold R.v16484, N.v16484.
  rewrite ?node_23575.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23577 (s : N.State) (i : N.Inputs) :
  R.v23577 (state s) (inputs i) = Zmod.unsigned (N.v23577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23577 s i)) at 1.
  unfold R.v23577, N.v23577.
  rewrite ?node_23572.
  rewrite ?node_23576.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23578 (s : N.State) (i : N.Inputs) :
  R.v23578 (state s) (inputs i) = Zmod.unsigned (N.v23578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23578 s i)) at 1.
  unfold R.v23578, N.v23578.
  unfold R.v6, N.v6.
  rewrite ?node_23577.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23579 (s : N.State) (i : N.Inputs) :
  R.v23579 (state s) (inputs i) = Zmod.unsigned (N.v23579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23579 s i)) at 1.
  unfold R.v23579, N.v23579.
  rewrite ?node_8682.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23580 (s : N.State) (i : N.Inputs) :
  R.v23580 (state s) (inputs i) = Zmod.unsigned (N.v23580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23580 s i)) at 1.
  unfold R.v23580, N.v23580.
  unfold R.v6, N.v6.
  rewrite ?node_8820.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23581 (s : N.State) (i : N.Inputs) :
  R.v23581 (state s) (inputs i) = Zmod.unsigned (N.v23581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23581 s i)) at 1.
  unfold R.v23581, N.v23581.
  rewrite ?node_23579.
  rewrite ?node_23580.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23582 (s : N.State) (i : N.Inputs) :
  R.v23582 (state s) (inputs i) = Zmod.unsigned (N.v23582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23582 s i)) at 1.
  unfold R.v23582, N.v23582.
  rewrite ?node_23578.
  rewrite ?node_23581.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23583 (s : N.State) (i : N.Inputs) :
  R.v23583 (state s) (inputs i) = Zmod.unsigned (N.v23583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23583 s i)) at 1.
  unfold R.v23583, N.v23583.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23584 (s : N.State) (i : N.Inputs) :
  R.v23584 (state s) (inputs i) = Zmod.unsigned (N.v23584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23584 s i)) at 1.
  unfold R.v23584, N.v23584.
  rewrite ?node_8686.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23585 (s : N.State) (i : N.Inputs) :
  R.v23585 (state s) (inputs i) = Zmod.unsigned (N.v23585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23585 s i)) at 1.
  unfold R.v23585, N.v23585.
  unfold R.v6, N.v6.
  rewrite !state_r785_nr_5F785.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r785_nr_5F785 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23586 (s : N.State) (i : N.Inputs) :
  R.v23586 (state s) (inputs i) = Zmod.unsigned (N.v23586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23586 s i)) at 1.
  unfold R.v23586, N.v23586.
  unfold R.v6, N.v6.
  rewrite ?node_8682.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23587 (s : N.State) (i : N.Inputs) :
  R.v23587 (state s) (inputs i) = Zmod.unsigned (N.v23587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23587 s i)) at 1.
  unfold R.v23587, N.v23587.
  rewrite ?node_23585.
  rewrite ?node_23586.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23588 (s : N.State) (i : N.Inputs) :
  R.v23588 (state s) (inputs i) = Zmod.unsigned (N.v23588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23588 s i)) at 1.
  unfold R.v23588, N.v23588.
  unfold R.v16484, N.v16484.
  rewrite ?node_23587.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23589 (s : N.State) (i : N.Inputs) :
  R.v23589 (state s) (inputs i) = Zmod.unsigned (N.v23589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23589 s i)) at 1.
  unfold R.v23589, N.v23589.
  rewrite ?node_23584.
  rewrite ?node_23588.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23590 (s : N.State) (i : N.Inputs) :
  R.v23590 (state s) (inputs i) = Zmod.unsigned (N.v23590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23590 s i)) at 1.
  unfold R.v23590, N.v23590.
  unfold R.v6, N.v6.
  rewrite ?node_23589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23591 (s : N.State) (i : N.Inputs) :
  R.v23591 (state s) (inputs i) = Zmod.unsigned (N.v23591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23591 s i)) at 1.
  unfold R.v23591, N.v23591.
  rewrite ?node_8687.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23592 (s : N.State) (i : N.Inputs) :
  R.v23592 (state s) (inputs i) = Zmod.unsigned (N.v23592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23592 s i)) at 1.
  unfold R.v23592, N.v23592.
  unfold R.v6, N.v6.
  rewrite ?node_8881.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23593 (s : N.State) (i : N.Inputs) :
  R.v23593 (state s) (inputs i) = Zmod.unsigned (N.v23593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23593 s i)) at 1.
  unfold R.v23593, N.v23593.
  rewrite ?node_23591.
  rewrite ?node_23592.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23594 (s : N.State) (i : N.Inputs) :
  R.v23594 (state s) (inputs i) = Zmod.unsigned (N.v23594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23594 s i)) at 1.
  unfold R.v23594, N.v23594.
  rewrite ?node_23590.
  rewrite ?node_23593.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23595 (s : N.State) (i : N.Inputs) :
  R.v23595 (state s) (inputs i) = Zmod.unsigned (N.v23595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23595 s i)) at 1.
  unfold R.v23595, N.v23595.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23596 (s : N.State) (i : N.Inputs) :
  R.v23596 (state s) (inputs i) = Zmod.unsigned (N.v23596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23596 s i)) at 1.
  unfold R.v23596, N.v23596.
  rewrite ?node_8693.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23597 (s : N.State) (i : N.Inputs) :
  R.v23597 (state s) (inputs i) = Zmod.unsigned (N.v23597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23597 s i)) at 1.
  unfold R.v23597, N.v23597.
  unfold R.v16463, N.v16463.
  rewrite !state_r789_nr_5F789.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r789_nr_5F789 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23598 (s : N.State) (i : N.Inputs) :
  R.v23598 (state s) (inputs i) = Zmod.unsigned (N.v23598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23598 s i)) at 1.
  unfold R.v23598, N.v23598.
  unfold R.v16463, N.v16463.
  rewrite !state_r788_nr_5F788.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r788_nr_5F788 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23599 (s : N.State) (i : N.Inputs) :
  R.v23599 (state s) (inputs i) = Zmod.unsigned (N.v23599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23599 s i)) at 1.
  unfold R.v23599, N.v23599.
  unfold R.v6, N.v6.
  rewrite !state_r787_nr_5F787.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r787_nr_5F787 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23600 (s : N.State) (i : N.Inputs) :
  R.v23600 (state s) (inputs i) = Zmod.unsigned (N.v23600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23600 s i)) at 1.
  unfold R.v23600, N.v23600.
  unfold R.v6, N.v6.
  rewrite !state_r786_nr_5F786.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r786_nr_5F786 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23601 (s : N.State) (i : N.Inputs) :
  R.v23601 (state s) (inputs i) = Zmod.unsigned (N.v23601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23601 s i)) at 1.
  unfold R.v23601, N.v23601.
  rewrite ?node_23599.
  rewrite ?node_23600.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23602 (s : N.State) (i : N.Inputs) :
  R.v23602 (state s) (inputs i) = Zmod.unsigned (N.v23602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23602 s i)) at 1.
  unfold R.v23602, N.v23602.
  unfold R.v16484, N.v16484.
  rewrite ?node_23601.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23603 (s : N.State) (i : N.Inputs) :
  R.v23603 (state s) (inputs i) = Zmod.unsigned (N.v23603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23603 s i)) at 1.
  unfold R.v23603, N.v23603.
  rewrite ?node_23596.
  rewrite ?node_23597.
  rewrite ?node_23598.
  rewrite ?node_23602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23604 (s : N.State) (i : N.Inputs) :
  R.v23604 (state s) (inputs i) = Zmod.unsigned (N.v23604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23604 s i)) at 1.
  unfold R.v23604, N.v23604.
  unfold R.v6, N.v6.
  rewrite ?node_23603.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23605 (s : N.State) (i : N.Inputs) :
  R.v23605 (state s) (inputs i) = Zmod.unsigned (N.v23605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23605 s i)) at 1.
  unfold R.v23605, N.v23605.
  rewrite ?node_8694.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23606 (s : N.State) (i : N.Inputs) :
  R.v23606 (state s) (inputs i) = Zmod.unsigned (N.v23606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23606 s i)) at 1.
  unfold R.v23606, N.v23606.
  unfold R.v6, N.v6.
  rewrite ?node_8827.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23607 (s : N.State) (i : N.Inputs) :
  R.v23607 (state s) (inputs i) = Zmod.unsigned (N.v23607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23607 s i)) at 1.
  unfold R.v23607, N.v23607.
  unfold R.v6, N.v6.
  rewrite ?node_8884.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23608 (s : N.State) (i : N.Inputs) :
  R.v23608 (state s) (inputs i) = Zmod.unsigned (N.v23608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23608 s i)) at 1.
  unfold R.v23608, N.v23608.
  rewrite ?node_23605.
  rewrite ?node_23606.
  rewrite ?node_23607.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23609 (s : N.State) (i : N.Inputs) :
  R.v23609 (state s) (inputs i) = Zmod.unsigned (N.v23609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23609 s i)) at 1.
  unfold R.v23609, N.v23609.
  rewrite ?node_23604.
  rewrite ?node_23608.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23610 (s : N.State) (i : N.Inputs) :
  R.v23610 (state s) (inputs i) = Zmod.unsigned (N.v23610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23610 s i)) at 1.
  unfold R.v23610, N.v23610.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23611 (s : N.State) (i : N.Inputs) :
  R.v23611 (state s) (inputs i) = Zmod.unsigned (N.v23611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23611 s i)) at 1.
  unfold R.v23611, N.v23611.
  unfold R.v16463, N.v16463.
  rewrite !state_r788_nr_5F788.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r788_nr_5F788 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23612 (s : N.State) (i : N.Inputs) :
  R.v23612 (state s) (inputs i) = Zmod.unsigned (N.v23612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23612 s i)) at 1.
  unfold R.v23612, N.v23612.
  unfold R.v6, N.v6.
  rewrite !state_r787_nr_5F787.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r787_nr_5F787 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23613 (s : N.State) (i : N.Inputs) :
  R.v23613 (state s) (inputs i) = Zmod.unsigned (N.v23613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23613 s i)) at 1.
  unfold R.v23613, N.v23613.
  unfold R.v6, N.v6.
  rewrite !state_r786_nr_5F786.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r786_nr_5F786 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23614 (s : N.State) (i : N.Inputs) :
  R.v23614 (state s) (inputs i) = Zmod.unsigned (N.v23614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23614 s i)) at 1.
  unfold R.v23614, N.v23614.
  rewrite ?node_23612.
  rewrite ?node_23613.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23615 (s : N.State) (i : N.Inputs) :
  R.v23615 (state s) (inputs i) = Zmod.unsigned (N.v23615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23615 s i)) at 1.
  unfold R.v23615, N.v23615.
  unfold R.v16484, N.v16484.
  rewrite ?node_23614.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23616 (s : N.State) (i : N.Inputs) :
  R.v23616 (state s) (inputs i) = Zmod.unsigned (N.v23616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23616 s i)) at 1.
  unfold R.v23616, N.v23616.
  rewrite ?node_23611.
  rewrite ?node_23615.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23617 (s : N.State) (i : N.Inputs) :
  R.v23617 (state s) (inputs i) = Zmod.unsigned (N.v23617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23617 s i)) at 1.
  unfold R.v23617, N.v23617.
  unfold R.v6, N.v6.
  rewrite ?node_23616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23618 (s : N.State) (i : N.Inputs) :
  R.v23618 (state s) (inputs i) = Zmod.unsigned (N.v23618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23618 s i)) at 1.
  unfold R.v23618, N.v23618.
  rewrite ?node_8689.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23619 (s : N.State) (i : N.Inputs) :
  R.v23619 (state s) (inputs i) = Zmod.unsigned (N.v23619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23619 s i)) at 1.
  unfold R.v23619, N.v23619.
  unfold R.v6, N.v6.
  rewrite ?node_8827.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23620 (s : N.State) (i : N.Inputs) :
  R.v23620 (state s) (inputs i) = Zmod.unsigned (N.v23620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23620 s i)) at 1.
  unfold R.v23620, N.v23620.
  rewrite ?node_23618.
  rewrite ?node_23619.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23621 (s : N.State) (i : N.Inputs) :
  R.v23621 (state s) (inputs i) = Zmod.unsigned (N.v23621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23621 s i)) at 1.
  unfold R.v23621, N.v23621.
  rewrite ?node_23617.
  rewrite ?node_23620.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23622 (s : N.State) (i : N.Inputs) :
  R.v23622 (state s) (inputs i) = Zmod.unsigned (N.v23622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23622 s i)) at 1.
  unfold R.v23622, N.v23622.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23623 (s : N.State) (i : N.Inputs) :
  R.v23623 (state s) (inputs i) = Zmod.unsigned (N.v23623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23623 s i)) at 1.
  unfold R.v23623, N.v23623.
  rewrite ?node_8693.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23624 (s : N.State) (i : N.Inputs) :
  R.v23624 (state s) (inputs i) = Zmod.unsigned (N.v23624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23624 s i)) at 1.
  unfold R.v23624, N.v23624.
  unfold R.v6, N.v6.
  rewrite !state_r789_nr_5F789.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r789_nr_5F789 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23625 (s : N.State) (i : N.Inputs) :
  R.v23625 (state s) (inputs i) = Zmod.unsigned (N.v23625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23625 s i)) at 1.
  unfold R.v23625, N.v23625.
  unfold R.v6, N.v6.
  rewrite ?node_8689.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23626 (s : N.State) (i : N.Inputs) :
  R.v23626 (state s) (inputs i) = Zmod.unsigned (N.v23626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23626 s i)) at 1.
  unfold R.v23626, N.v23626.
  rewrite ?node_23624.
  rewrite ?node_23625.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23627 (s : N.State) (i : N.Inputs) :
  R.v23627 (state s) (inputs i) = Zmod.unsigned (N.v23627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23627 s i)) at 1.
  unfold R.v23627, N.v23627.
  unfold R.v16484, N.v16484.
  rewrite ?node_23626.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23628 (s : N.State) (i : N.Inputs) :
  R.v23628 (state s) (inputs i) = Zmod.unsigned (N.v23628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23628 s i)) at 1.
  unfold R.v23628, N.v23628.
  rewrite ?node_23623.
  rewrite ?node_23627.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23629 (s : N.State) (i : N.Inputs) :
  R.v23629 (state s) (inputs i) = Zmod.unsigned (N.v23629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23629 s i)) at 1.
  unfold R.v23629, N.v23629.
  unfold R.v6, N.v6.
  rewrite ?node_23628.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23630 (s : N.State) (i : N.Inputs) :
  R.v23630 (state s) (inputs i) = Zmod.unsigned (N.v23630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23630 s i)) at 1.
  unfold R.v23630, N.v23630.
  rewrite ?node_8694.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23631 (s : N.State) (i : N.Inputs) :
  R.v23631 (state s) (inputs i) = Zmod.unsigned (N.v23631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23631 s i)) at 1.
  unfold R.v23631, N.v23631.
  unfold R.v6, N.v6.
  rewrite ?node_8884.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23632 (s : N.State) (i : N.Inputs) :
  R.v23632 (state s) (inputs i) = Zmod.unsigned (N.v23632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23632 s i)) at 1.
  unfold R.v23632, N.v23632.
  rewrite ?node_23630.
  rewrite ?node_23631.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23633 (s : N.State) (i : N.Inputs) :
  R.v23633 (state s) (inputs i) = Zmod.unsigned (N.v23633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23633 s i)) at 1.
  unfold R.v23633, N.v23633.
  rewrite ?node_23629.
  rewrite ?node_23632.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23634 (s : N.State) (i : N.Inputs) :
  R.v23634 (state s) (inputs i) = Zmod.unsigned (N.v23634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23634 s i)) at 1.
  unfold R.v23634, N.v23634.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23635 (s : N.State) (i : N.Inputs) :
  R.v23635 (state s) (inputs i) = Zmod.unsigned (N.v23635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23635 s i)) at 1.
  unfold R.v23635, N.v23635.
  rewrite ?node_8701.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23636 (s : N.State) (i : N.Inputs) :
  R.v23636 (state s) (inputs i) = Zmod.unsigned (N.v23636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23636 s i)) at 1.
  unfold R.v23636, N.v23636.
  unfold R.v16463, N.v16463.
  rewrite !state_r793_nr_5F793.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r793_nr_5F793 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23637 (s : N.State) (i : N.Inputs) :
  R.v23637 (state s) (inputs i) = Zmod.unsigned (N.v23637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23637 s i)) at 1.
  unfold R.v23637, N.v23637.
  unfold R.v16463, N.v16463.
  rewrite !state_r792_nr_5F792.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r792_nr_5F792 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23638 (s : N.State) (i : N.Inputs) :
  R.v23638 (state s) (inputs i) = Zmod.unsigned (N.v23638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23638 s i)) at 1.
  unfold R.v23638, N.v23638.
  unfold R.v6, N.v6.
  rewrite !state_r791_nr_5F791.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r791_nr_5F791 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23639 (s : N.State) (i : N.Inputs) :
  R.v23639 (state s) (inputs i) = Zmod.unsigned (N.v23639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23639 s i)) at 1.
  unfold R.v23639, N.v23639.
  unfold R.v6, N.v6.
  rewrite !state_r790_nr_5F790.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r790_nr_5F790 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23640 (s : N.State) (i : N.Inputs) :
  R.v23640 (state s) (inputs i) = Zmod.unsigned (N.v23640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23640 s i)) at 1.
  unfold R.v23640, N.v23640.
  rewrite ?node_23638.
  rewrite ?node_23639.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23641 (s : N.State) (i : N.Inputs) :
  R.v23641 (state s) (inputs i) = Zmod.unsigned (N.v23641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23641 s i)) at 1.
  unfold R.v23641, N.v23641.
  unfold R.v16484, N.v16484.
  rewrite ?node_23640.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23642 (s : N.State) (i : N.Inputs) :
  R.v23642 (state s) (inputs i) = Zmod.unsigned (N.v23642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23642 s i)) at 1.
  unfold R.v23642, N.v23642.
  rewrite ?node_23635.
  rewrite ?node_23636.
  rewrite ?node_23637.
  rewrite ?node_23641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23643 (s : N.State) (i : N.Inputs) :
  R.v23643 (state s) (inputs i) = Zmod.unsigned (N.v23643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23643 s i)) at 1.
  unfold R.v23643, N.v23643.
  unfold R.v6, N.v6.
  rewrite ?node_23642.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23644 (s : N.State) (i : N.Inputs) :
  R.v23644 (state s) (inputs i) = Zmod.unsigned (N.v23644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23644 s i)) at 1.
  unfold R.v23644, N.v23644.
  rewrite ?node_8702.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23645 (s : N.State) (i : N.Inputs) :
  R.v23645 (state s) (inputs i) = Zmod.unsigned (N.v23645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23645 s i)) at 1.
  unfold R.v23645, N.v23645.
  unfold R.v6, N.v6.
  rewrite ?node_8835.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23646 (s : N.State) (i : N.Inputs) :
  R.v23646 (state s) (inputs i) = Zmod.unsigned (N.v23646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23646 s i)) at 1.
  unfold R.v23646, N.v23646.
  unfold R.v6, N.v6.
  rewrite ?node_8888.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23647 (s : N.State) (i : N.Inputs) :
  R.v23647 (state s) (inputs i) = Zmod.unsigned (N.v23647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23647 s i)) at 1.
  unfold R.v23647, N.v23647.
  rewrite ?node_23644.
  rewrite ?node_23645.
  rewrite ?node_23646.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23648 (s : N.State) (i : N.Inputs) :
  R.v23648 (state s) (inputs i) = Zmod.unsigned (N.v23648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23648 s i)) at 1.
  unfold R.v23648, N.v23648.
  rewrite ?node_23643.
  rewrite ?node_23647.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23649 (s : N.State) (i : N.Inputs) :
  R.v23649 (state s) (inputs i) = Zmod.unsigned (N.v23649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23649 s i)) at 1.
  unfold R.v23649, N.v23649.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23650 (s : N.State) (i : N.Inputs) :
  R.v23650 (state s) (inputs i) = Zmod.unsigned (N.v23650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23650 s i)) at 1.
  unfold R.v23650, N.v23650.
  unfold R.v16463, N.v16463.
  rewrite !state_r792_nr_5F792.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r792_nr_5F792 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23651 (s : N.State) (i : N.Inputs) :
  R.v23651 (state s) (inputs i) = Zmod.unsigned (N.v23651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23651 s i)) at 1.
  unfold R.v23651, N.v23651.
  unfold R.v6, N.v6.
  rewrite !state_r791_nr_5F791.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r791_nr_5F791 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23652 (s : N.State) (i : N.Inputs) :
  R.v23652 (state s) (inputs i) = Zmod.unsigned (N.v23652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23652 s i)) at 1.
  unfold R.v23652, N.v23652.
  unfold R.v6, N.v6.
  rewrite !state_r790_nr_5F790.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r790_nr_5F790 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23653 (s : N.State) (i : N.Inputs) :
  R.v23653 (state s) (inputs i) = Zmod.unsigned (N.v23653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23653 s i)) at 1.
  unfold R.v23653, N.v23653.
  rewrite ?node_23651.
  rewrite ?node_23652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23654 (s : N.State) (i : N.Inputs) :
  R.v23654 (state s) (inputs i) = Zmod.unsigned (N.v23654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23654 s i)) at 1.
  unfold R.v23654, N.v23654.
  unfold R.v16484, N.v16484.
  rewrite ?node_23653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23655 (s : N.State) (i : N.Inputs) :
  R.v23655 (state s) (inputs i) = Zmod.unsigned (N.v23655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23655 s i)) at 1.
  unfold R.v23655, N.v23655.
  rewrite ?node_23650.
  rewrite ?node_23654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23656 (s : N.State) (i : N.Inputs) :
  R.v23656 (state s) (inputs i) = Zmod.unsigned (N.v23656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23656 s i)) at 1.
  unfold R.v23656, N.v23656.
  unfold R.v6, N.v6.
  rewrite ?node_23655.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23657 (s : N.State) (i : N.Inputs) :
  R.v23657 (state s) (inputs i) = Zmod.unsigned (N.v23657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23657 s i)) at 1.
  unfold R.v23657, N.v23657.
  rewrite ?node_8697.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23658 (s : N.State) (i : N.Inputs) :
  R.v23658 (state s) (inputs i) = Zmod.unsigned (N.v23658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23658 s i)) at 1.
  unfold R.v23658, N.v23658.
  unfold R.v6, N.v6.
  rewrite ?node_8835.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23659 (s : N.State) (i : N.Inputs) :
  R.v23659 (state s) (inputs i) = Zmod.unsigned (N.v23659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23659 s i)) at 1.
  unfold R.v23659, N.v23659.
  rewrite ?node_23657.
  rewrite ?node_23658.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23660 (s : N.State) (i : N.Inputs) :
  R.v23660 (state s) (inputs i) = Zmod.unsigned (N.v23660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23660 s i)) at 1.
  unfold R.v23660, N.v23660.
  rewrite ?node_23656.
  rewrite ?node_23659.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23661 (s : N.State) (i : N.Inputs) :
  R.v23661 (state s) (inputs i) = Zmod.unsigned (N.v23661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23661 s i)) at 1.
  unfold R.v23661, N.v23661.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23662 (s : N.State) (i : N.Inputs) :
  R.v23662 (state s) (inputs i) = Zmod.unsigned (N.v23662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23662 s i)) at 1.
  unfold R.v23662, N.v23662.
  rewrite ?node_8701.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23663 (s : N.State) (i : N.Inputs) :
  R.v23663 (state s) (inputs i) = Zmod.unsigned (N.v23663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23663 s i)) at 1.
  unfold R.v23663, N.v23663.
  unfold R.v6, N.v6.
  rewrite !state_r793_nr_5F793.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r793_nr_5F793 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23664 (s : N.State) (i : N.Inputs) :
  R.v23664 (state s) (inputs i) = Zmod.unsigned (N.v23664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23664 s i)) at 1.
  unfold R.v23664, N.v23664.
  unfold R.v6, N.v6.
  rewrite ?node_8697.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23665 (s : N.State) (i : N.Inputs) :
  R.v23665 (state s) (inputs i) = Zmod.unsigned (N.v23665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23665 s i)) at 1.
  unfold R.v23665, N.v23665.
  rewrite ?node_23663.
  rewrite ?node_23664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23666 (s : N.State) (i : N.Inputs) :
  R.v23666 (state s) (inputs i) = Zmod.unsigned (N.v23666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23666 s i)) at 1.
  unfold R.v23666, N.v23666.
  unfold R.v16484, N.v16484.
  rewrite ?node_23665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23667 (s : N.State) (i : N.Inputs) :
  R.v23667 (state s) (inputs i) = Zmod.unsigned (N.v23667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23667 s i)) at 1.
  unfold R.v23667, N.v23667.
  rewrite ?node_23662.
  rewrite ?node_23666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23668 (s : N.State) (i : N.Inputs) :
  R.v23668 (state s) (inputs i) = Zmod.unsigned (N.v23668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23668 s i)) at 1.
  unfold R.v23668, N.v23668.
  unfold R.v6, N.v6.
  rewrite ?node_23667.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23669 (s : N.State) (i : N.Inputs) :
  R.v23669 (state s) (inputs i) = Zmod.unsigned (N.v23669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23669 s i)) at 1.
  unfold R.v23669, N.v23669.
  rewrite ?node_8702.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23670 (s : N.State) (i : N.Inputs) :
  R.v23670 (state s) (inputs i) = Zmod.unsigned (N.v23670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23670 s i)) at 1.
  unfold R.v23670, N.v23670.
  unfold R.v6, N.v6.
  rewrite ?node_8888.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23671 (s : N.State) (i : N.Inputs) :
  R.v23671 (state s) (inputs i) = Zmod.unsigned (N.v23671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23671 s i)) at 1.
  unfold R.v23671, N.v23671.
  rewrite ?node_23669.
  rewrite ?node_23670.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23672 (s : N.State) (i : N.Inputs) :
  R.v23672 (state s) (inputs i) = Zmod.unsigned (N.v23672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23672 s i)) at 1.
  unfold R.v23672, N.v23672.
  rewrite ?node_23668.
  rewrite ?node_23671.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23673 (s : N.State) (i : N.Inputs) :
  R.v23673 (state s) (inputs i) = Zmod.unsigned (N.v23673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23673 s i)) at 1.
  unfold R.v23673, N.v23673.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23674 (s : N.State) (i : N.Inputs) :
  R.v23674 (state s) (inputs i) = Zmod.unsigned (N.v23674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23674 s i)) at 1.
  unfold R.v23674, N.v23674.
  rewrite ?node_8709.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23675 (s : N.State) (i : N.Inputs) :
  R.v23675 (state s) (inputs i) = Zmod.unsigned (N.v23675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23675 s i)) at 1.
  unfold R.v23675, N.v23675.
  unfold R.v16463, N.v16463.
  rewrite !state_r797_nr_5F797.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r797_nr_5F797 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23676 (s : N.State) (i : N.Inputs) :
  R.v23676 (state s) (inputs i) = Zmod.unsigned (N.v23676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23676 s i)) at 1.
  unfold R.v23676, N.v23676.
  unfold R.v16463, N.v16463.
  rewrite !state_r796_nr_5F796.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r796_nr_5F796 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23677 (s : N.State) (i : N.Inputs) :
  R.v23677 (state s) (inputs i) = Zmod.unsigned (N.v23677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23677 s i)) at 1.
  unfold R.v23677, N.v23677.
  unfold R.v6, N.v6.
  rewrite !state_r795_nr_5F795.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r795_nr_5F795 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23678 (s : N.State) (i : N.Inputs) :
  R.v23678 (state s) (inputs i) = Zmod.unsigned (N.v23678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23678 s i)) at 1.
  unfold R.v23678, N.v23678.
  unfold R.v6, N.v6.
  rewrite !state_r794_nr_5F794.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r794_nr_5F794 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23679 (s : N.State) (i : N.Inputs) :
  R.v23679 (state s) (inputs i) = Zmod.unsigned (N.v23679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23679 s i)) at 1.
  unfold R.v23679, N.v23679.
  rewrite ?node_23677.
  rewrite ?node_23678.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23680 (s : N.State) (i : N.Inputs) :
  R.v23680 (state s) (inputs i) = Zmod.unsigned (N.v23680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23680 s i)) at 1.
  unfold R.v23680, N.v23680.
  unfold R.v16484, N.v16484.
  rewrite ?node_23679.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23681 (s : N.State) (i : N.Inputs) :
  R.v23681 (state s) (inputs i) = Zmod.unsigned (N.v23681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23681 s i)) at 1.
  unfold R.v23681, N.v23681.
  rewrite ?node_23674.
  rewrite ?node_23675.
  rewrite ?node_23676.
  rewrite ?node_23680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23682 (s : N.State) (i : N.Inputs) :
  R.v23682 (state s) (inputs i) = Zmod.unsigned (N.v23682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23682 s i)) at 1.
  unfold R.v23682, N.v23682.
  unfold R.v6, N.v6.
  rewrite ?node_23681.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23683 (s : N.State) (i : N.Inputs) :
  R.v23683 (state s) (inputs i) = Zmod.unsigned (N.v23683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23683 s i)) at 1.
  unfold R.v23683, N.v23683.
  rewrite ?node_8710.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23684 (s : N.State) (i : N.Inputs) :
  R.v23684 (state s) (inputs i) = Zmod.unsigned (N.v23684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23684 s i)) at 1.
  unfold R.v23684, N.v23684.
  unfold R.v6, N.v6.
  rewrite ?node_8843.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23685 (s : N.State) (i : N.Inputs) :
  R.v23685 (state s) (inputs i) = Zmod.unsigned (N.v23685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23685 s i)) at 1.
  unfold R.v23685, N.v23685.
  unfold R.v6, N.v6.
  rewrite ?node_8892.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23686 (s : N.State) (i : N.Inputs) :
  R.v23686 (state s) (inputs i) = Zmod.unsigned (N.v23686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23686 s i)) at 1.
  unfold R.v23686, N.v23686.
  rewrite ?node_23683.
  rewrite ?node_23684.
  rewrite ?node_23685.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23687 (s : N.State) (i : N.Inputs) :
  R.v23687 (state s) (inputs i) = Zmod.unsigned (N.v23687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23687 s i)) at 1.
  unfold R.v23687, N.v23687.
  rewrite ?node_23682.
  rewrite ?node_23686.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23688 (s : N.State) (i : N.Inputs) :
  R.v23688 (state s) (inputs i) = Zmod.unsigned (N.v23688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23688 s i)) at 1.
  unfold R.v23688, N.v23688.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23689 (s : N.State) (i : N.Inputs) :
  R.v23689 (state s) (inputs i) = Zmod.unsigned (N.v23689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23689 s i)) at 1.
  unfold R.v23689, N.v23689.
  unfold R.v16463, N.v16463.
  rewrite !state_r796_nr_5F796.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r796_nr_5F796 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23690 (s : N.State) (i : N.Inputs) :
  R.v23690 (state s) (inputs i) = Zmod.unsigned (N.v23690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23690 s i)) at 1.
  unfold R.v23690, N.v23690.
  unfold R.v6, N.v6.
  rewrite !state_r795_nr_5F795.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r795_nr_5F795 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23691 (s : N.State) (i : N.Inputs) :
  R.v23691 (state s) (inputs i) = Zmod.unsigned (N.v23691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23691 s i)) at 1.
  unfold R.v23691, N.v23691.
  unfold R.v6, N.v6.
  rewrite !state_r794_nr_5F794.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r794_nr_5F794 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23692 (s : N.State) (i : N.Inputs) :
  R.v23692 (state s) (inputs i) = Zmod.unsigned (N.v23692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23692 s i)) at 1.
  unfold R.v23692, N.v23692.
  rewrite ?node_23690.
  rewrite ?node_23691.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23693 (s : N.State) (i : N.Inputs) :
  R.v23693 (state s) (inputs i) = Zmod.unsigned (N.v23693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23693 s i)) at 1.
  unfold R.v23693, N.v23693.
  unfold R.v16484, N.v16484.
  rewrite ?node_23692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23694 (s : N.State) (i : N.Inputs) :
  R.v23694 (state s) (inputs i) = Zmod.unsigned (N.v23694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23694 s i)) at 1.
  unfold R.v23694, N.v23694.
  rewrite ?node_23689.
  rewrite ?node_23693.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23695 (s : N.State) (i : N.Inputs) :
  R.v23695 (state s) (inputs i) = Zmod.unsigned (N.v23695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23695 s i)) at 1.
  unfold R.v23695, N.v23695.
  unfold R.v6, N.v6.
  rewrite ?node_23694.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23696 (s : N.State) (i : N.Inputs) :
  R.v23696 (state s) (inputs i) = Zmod.unsigned (N.v23696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23696 s i)) at 1.
  unfold R.v23696, N.v23696.
  rewrite ?node_8705.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23697 (s : N.State) (i : N.Inputs) :
  R.v23697 (state s) (inputs i) = Zmod.unsigned (N.v23697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23697 s i)) at 1.
  unfold R.v23697, N.v23697.
  unfold R.v6, N.v6.
  rewrite ?node_8843.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23698 (s : N.State) (i : N.Inputs) :
  R.v23698 (state s) (inputs i) = Zmod.unsigned (N.v23698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23698 s i)) at 1.
  unfold R.v23698, N.v23698.
  rewrite ?node_23696.
  rewrite ?node_23697.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23699 (s : N.State) (i : N.Inputs) :
  R.v23699 (state s) (inputs i) = Zmod.unsigned (N.v23699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23699 s i)) at 1.
  unfold R.v23699, N.v23699.
  rewrite ?node_23695.
  rewrite ?node_23698.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23700 (s : N.State) (i : N.Inputs) :
  R.v23700 (state s) (inputs i) = Zmod.unsigned (N.v23700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23700 s i)) at 1.
  unfold R.v23700, N.v23700.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23701 (s : N.State) (i : N.Inputs) :
  R.v23701 (state s) (inputs i) = Zmod.unsigned (N.v23701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23701 s i)) at 1.
  unfold R.v23701, N.v23701.
  rewrite ?node_8709.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23702 (s : N.State) (i : N.Inputs) :
  R.v23702 (state s) (inputs i) = Zmod.unsigned (N.v23702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23702 s i)) at 1.
  unfold R.v23702, N.v23702.
  unfold R.v6, N.v6.
  rewrite !state_r797_nr_5F797.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r797_nr_5F797 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23703 (s : N.State) (i : N.Inputs) :
  R.v23703 (state s) (inputs i) = Zmod.unsigned (N.v23703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23703 s i)) at 1.
  unfold R.v23703, N.v23703.
  unfold R.v6, N.v6.
  rewrite ?node_8705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23704 (s : N.State) (i : N.Inputs) :
  R.v23704 (state s) (inputs i) = Zmod.unsigned (N.v23704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23704 s i)) at 1.
  unfold R.v23704, N.v23704.
  rewrite ?node_23702.
  rewrite ?node_23703.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23705 (s : N.State) (i : N.Inputs) :
  R.v23705 (state s) (inputs i) = Zmod.unsigned (N.v23705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23705 s i)) at 1.
  unfold R.v23705, N.v23705.
  unfold R.v16484, N.v16484.
  rewrite ?node_23704.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23706 (s : N.State) (i : N.Inputs) :
  R.v23706 (state s) (inputs i) = Zmod.unsigned (N.v23706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23706 s i)) at 1.
  unfold R.v23706, N.v23706.
  rewrite ?node_23701.
  rewrite ?node_23705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23707 (s : N.State) (i : N.Inputs) :
  R.v23707 (state s) (inputs i) = Zmod.unsigned (N.v23707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23707 s i)) at 1.
  unfold R.v23707, N.v23707.
  unfold R.v6, N.v6.
  rewrite ?node_23706.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23708 (s : N.State) (i : N.Inputs) :
  R.v23708 (state s) (inputs i) = Zmod.unsigned (N.v23708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23708 s i)) at 1.
  unfold R.v23708, N.v23708.
  rewrite ?node_8710.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23709 (s : N.State) (i : N.Inputs) :
  R.v23709 (state s) (inputs i) = Zmod.unsigned (N.v23709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23709 s i)) at 1.
  unfold R.v23709, N.v23709.
  unfold R.v6, N.v6.
  rewrite ?node_8892.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23710 (s : N.State) (i : N.Inputs) :
  R.v23710 (state s) (inputs i) = Zmod.unsigned (N.v23710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23710 s i)) at 1.
  unfold R.v23710, N.v23710.
  rewrite ?node_23708.
  rewrite ?node_23709.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23711 (s : N.State) (i : N.Inputs) :
  R.v23711 (state s) (inputs i) = Zmod.unsigned (N.v23711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23711 s i)) at 1.
  unfold R.v23711, N.v23711.
  rewrite ?node_23707.
  rewrite ?node_23710.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23712 (s : N.State) (i : N.Inputs) :
  R.v23712 (state s) (inputs i) = Zmod.unsigned (N.v23712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23712 s i)) at 1.
  unfold R.v23712, N.v23712.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23713 (s : N.State) (i : N.Inputs) :
  R.v23713 (state s) (inputs i) = Zmod.unsigned (N.v23713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23713 s i)) at 1.
  unfold R.v23713, N.v23713.
  rewrite ?node_8721.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23714 (s : N.State) (i : N.Inputs) :
  R.v23714 (state s) (inputs i) = Zmod.unsigned (N.v23714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23714 s i)) at 1.
  unfold R.v23714, N.v23714.
  unfold R.v16463, N.v16463.
  rewrite !state_r801_nr_5F801.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r801_nr_5F801 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23715 (s : N.State) (i : N.Inputs) :
  R.v23715 (state s) (inputs i) = Zmod.unsigned (N.v23715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23715 s i)) at 1.
  unfold R.v23715, N.v23715.
  unfold R.v16463, N.v16463.
  rewrite !state_r800_nr_5F800.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r800_nr_5F800 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23716 (s : N.State) (i : N.Inputs) :
  R.v23716 (state s) (inputs i) = Zmod.unsigned (N.v23716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23716 s i)) at 1.
  unfold R.v23716, N.v23716.
  unfold R.v6, N.v6.
  rewrite !state_r799_nr_5F799.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r799_nr_5F799 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23717 (s : N.State) (i : N.Inputs) :
  R.v23717 (state s) (inputs i) = Zmod.unsigned (N.v23717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23717 s i)) at 1.
  unfold R.v23717, N.v23717.
  unfold R.v6, N.v6.
  rewrite !state_r798_nr_5F798.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r798_nr_5F798 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23718 (s : N.State) (i : N.Inputs) :
  R.v23718 (state s) (inputs i) = Zmod.unsigned (N.v23718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23718 s i)) at 1.
  unfold R.v23718, N.v23718.
  rewrite ?node_23716.
  rewrite ?node_23717.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23719 (s : N.State) (i : N.Inputs) :
  R.v23719 (state s) (inputs i) = Zmod.unsigned (N.v23719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23719 s i)) at 1.
  unfold R.v23719, N.v23719.
  unfold R.v16484, N.v16484.
  rewrite ?node_23718.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23720 (s : N.State) (i : N.Inputs) :
  R.v23720 (state s) (inputs i) = Zmod.unsigned (N.v23720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23720 s i)) at 1.
  unfold R.v23720, N.v23720.
  rewrite ?node_23713.
  rewrite ?node_23714.
  rewrite ?node_23715.
  rewrite ?node_23719.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23721 (s : N.State) (i : N.Inputs) :
  R.v23721 (state s) (inputs i) = Zmod.unsigned (N.v23721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23721 s i)) at 1.
  unfold R.v23721, N.v23721.
  unfold R.v6, N.v6.
  rewrite ?node_23720.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23722 (s : N.State) (i : N.Inputs) :
  R.v23722 (state s) (inputs i) = Zmod.unsigned (N.v23722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23722 s i)) at 1.
  unfold R.v23722, N.v23722.
  rewrite ?node_8722.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23723 (s : N.State) (i : N.Inputs) :
  R.v23723 (state s) (inputs i) = Zmod.unsigned (N.v23723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23723 s i)) at 1.
  unfold R.v23723, N.v23723.
  unfold R.v6, N.v6.
  rewrite ?node_8855.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23724 (s : N.State) (i : N.Inputs) :
  R.v23724 (state s) (inputs i) = Zmod.unsigned (N.v23724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23724 s i)) at 1.
  unfold R.v23724, N.v23724.
  unfold R.v6, N.v6.
  rewrite ?node_8901.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23725 (s : N.State) (i : N.Inputs) :
  R.v23725 (state s) (inputs i) = Zmod.unsigned (N.v23725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23725 s i)) at 1.
  unfold R.v23725, N.v23725.
  rewrite ?node_23722.
  rewrite ?node_23723.
  rewrite ?node_23724.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23726 (s : N.State) (i : N.Inputs) :
  R.v23726 (state s) (inputs i) = Zmod.unsigned (N.v23726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23726 s i)) at 1.
  unfold R.v23726, N.v23726.
  rewrite ?node_23721.
  rewrite ?node_23725.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23727 (s : N.State) (i : N.Inputs) :
  R.v23727 (state s) (inputs i) = Zmod.unsigned (N.v23727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23727 s i)) at 1.
  unfold R.v23727, N.v23727.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23728 (s : N.State) (i : N.Inputs) :
  R.v23728 (state s) (inputs i) = Zmod.unsigned (N.v23728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23728 s i)) at 1.
  unfold R.v23728, N.v23728.
  unfold R.v16463, N.v16463.
  rewrite !state_r800_nr_5F800.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r800_nr_5F800 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23729 (s : N.State) (i : N.Inputs) :
  R.v23729 (state s) (inputs i) = Zmod.unsigned (N.v23729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23729 s i)) at 1.
  unfold R.v23729, N.v23729.
  unfold R.v6, N.v6.
  rewrite !state_r799_nr_5F799.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r799_nr_5F799 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23730 (s : N.State) (i : N.Inputs) :
  R.v23730 (state s) (inputs i) = Zmod.unsigned (N.v23730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23730 s i)) at 1.
  unfold R.v23730, N.v23730.
  unfold R.v6, N.v6.
  rewrite !state_r798_nr_5F798.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r798_nr_5F798 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23731 (s : N.State) (i : N.Inputs) :
  R.v23731 (state s) (inputs i) = Zmod.unsigned (N.v23731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23731 s i)) at 1.
  unfold R.v23731, N.v23731.
  rewrite ?node_23729.
  rewrite ?node_23730.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23732 (s : N.State) (i : N.Inputs) :
  R.v23732 (state s) (inputs i) = Zmod.unsigned (N.v23732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23732 s i)) at 1.
  unfold R.v23732, N.v23732.
  unfold R.v16484, N.v16484.
  rewrite ?node_23731.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23733 (s : N.State) (i : N.Inputs) :
  R.v23733 (state s) (inputs i) = Zmod.unsigned (N.v23733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23733 s i)) at 1.
  unfold R.v23733, N.v23733.
  rewrite ?node_23728.
  rewrite ?node_23732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23734 (s : N.State) (i : N.Inputs) :
  R.v23734 (state s) (inputs i) = Zmod.unsigned (N.v23734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23734 s i)) at 1.
  unfold R.v23734, N.v23734.
  unfold R.v6, N.v6.
  rewrite ?node_23733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23735 (s : N.State) (i : N.Inputs) :
  R.v23735 (state s) (inputs i) = Zmod.unsigned (N.v23735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23735 s i)) at 1.
  unfold R.v23735, N.v23735.
  rewrite ?node_8717.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23736 (s : N.State) (i : N.Inputs) :
  R.v23736 (state s) (inputs i) = Zmod.unsigned (N.v23736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23736 s i)) at 1.
  unfold R.v23736, N.v23736.
  unfold R.v6, N.v6.
  rewrite ?node_8855.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23737 (s : N.State) (i : N.Inputs) :
  R.v23737 (state s) (inputs i) = Zmod.unsigned (N.v23737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23737 s i)) at 1.
  unfold R.v23737, N.v23737.
  rewrite ?node_23735.
  rewrite ?node_23736.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23738 (s : N.State) (i : N.Inputs) :
  R.v23738 (state s) (inputs i) = Zmod.unsigned (N.v23738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23738 s i)) at 1.
  unfold R.v23738, N.v23738.
  rewrite ?node_23734.
  rewrite ?node_23737.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23739 (s : N.State) (i : N.Inputs) :
  R.v23739 (state s) (inputs i) = Zmod.unsigned (N.v23739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23739 s i)) at 1.
  unfold R.v23739, N.v23739.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23740 (s : N.State) (i : N.Inputs) :
  R.v23740 (state s) (inputs i) = Zmod.unsigned (N.v23740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23740 s i)) at 1.
  unfold R.v23740, N.v23740.
  rewrite ?node_8721.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23741 (s : N.State) (i : N.Inputs) :
  R.v23741 (state s) (inputs i) = Zmod.unsigned (N.v23741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23741 s i)) at 1.
  unfold R.v23741, N.v23741.
  unfold R.v6, N.v6.
  rewrite !state_r801_nr_5F801.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r801_nr_5F801 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23742 (s : N.State) (i : N.Inputs) :
  R.v23742 (state s) (inputs i) = Zmod.unsigned (N.v23742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23742 s i)) at 1.
  unfold R.v23742, N.v23742.
  unfold R.v6, N.v6.
  rewrite ?node_8717.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23743 (s : N.State) (i : N.Inputs) :
  R.v23743 (state s) (inputs i) = Zmod.unsigned (N.v23743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23743 s i)) at 1.
  unfold R.v23743, N.v23743.
  rewrite ?node_23741.
  rewrite ?node_23742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23744 (s : N.State) (i : N.Inputs) :
  R.v23744 (state s) (inputs i) = Zmod.unsigned (N.v23744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23744 s i)) at 1.
  unfold R.v23744, N.v23744.
  unfold R.v16484, N.v16484.
  rewrite ?node_23743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23745 (s : N.State) (i : N.Inputs) :
  R.v23745 (state s) (inputs i) = Zmod.unsigned (N.v23745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23745 s i)) at 1.
  unfold R.v23745, N.v23745.
  rewrite ?node_23740.
  rewrite ?node_23744.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23746 (s : N.State) (i : N.Inputs) :
  R.v23746 (state s) (inputs i) = Zmod.unsigned (N.v23746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23746 s i)) at 1.
  unfold R.v23746, N.v23746.
  unfold R.v6, N.v6.
  rewrite ?node_23745.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23747 (s : N.State) (i : N.Inputs) :
  R.v23747 (state s) (inputs i) = Zmod.unsigned (N.v23747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23747 s i)) at 1.
  unfold R.v23747, N.v23747.
  rewrite ?node_8722.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23748 (s : N.State) (i : N.Inputs) :
  R.v23748 (state s) (inputs i) = Zmod.unsigned (N.v23748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23748 s i)) at 1.
  unfold R.v23748, N.v23748.
  unfold R.v6, N.v6.
  rewrite ?node_8901.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23749 (s : N.State) (i : N.Inputs) :
  R.v23749 (state s) (inputs i) = Zmod.unsigned (N.v23749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23749 s i)) at 1.
  unfold R.v23749, N.v23749.
  rewrite ?node_23747.
  rewrite ?node_23748.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23750 (s : N.State) (i : N.Inputs) :
  R.v23750 (state s) (inputs i) = Zmod.unsigned (N.v23750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23750 s i)) at 1.
  unfold R.v23750, N.v23750.
  rewrite ?node_23746.
  rewrite ?node_23749.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23751 (s : N.State) (i : N.Inputs) :
  R.v23751 (state s) (inputs i) = Zmod.unsigned (N.v23751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23751 s i)) at 1.
  unfold R.v23751, N.v23751.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23752 (s : N.State) (i : N.Inputs) :
  R.v23752 (state s) (inputs i) = Zmod.unsigned (N.v23752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23752 s i)) at 1.
  unfold R.v23752, N.v23752.
  rewrite ?node_8728.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23753 (s : N.State) (i : N.Inputs) :
  R.v23753 (state s) (inputs i) = Zmod.unsigned (N.v23753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23753 s i)) at 1.
  unfold R.v23753, N.v23753.
  unfold R.v16463, N.v16463.
  rewrite !state_r805_nr_5F805.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r805_nr_5F805 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23754 (s : N.State) (i : N.Inputs) :
  R.v23754 (state s) (inputs i) = Zmod.unsigned (N.v23754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23754 s i)) at 1.
  unfold R.v23754, N.v23754.
  unfold R.v16463, N.v16463.
  rewrite !state_r804_nr_5F804.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r804_nr_5F804 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23755 (s : N.State) (i : N.Inputs) :
  R.v23755 (state s) (inputs i) = Zmod.unsigned (N.v23755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23755 s i)) at 1.
  unfold R.v23755, N.v23755.
  unfold R.v6, N.v6.
  rewrite !state_r803_nr_5F803.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r803_nr_5F803 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23756 (s : N.State) (i : N.Inputs) :
  R.v23756 (state s) (inputs i) = Zmod.unsigned (N.v23756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23756 s i)) at 1.
  unfold R.v23756, N.v23756.
  unfold R.v6, N.v6.
  rewrite !state_r802_nr_5F802.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r802_nr_5F802 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23757 (s : N.State) (i : N.Inputs) :
  R.v23757 (state s) (inputs i) = Zmod.unsigned (N.v23757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23757 s i)) at 1.
  unfold R.v23757, N.v23757.
  rewrite ?node_23755.
  rewrite ?node_23756.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23758 (s : N.State) (i : N.Inputs) :
  R.v23758 (state s) (inputs i) = Zmod.unsigned (N.v23758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23758 s i)) at 1.
  unfold R.v23758, N.v23758.
  unfold R.v16484, N.v16484.
  rewrite ?node_23757.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23759 (s : N.State) (i : N.Inputs) :
  R.v23759 (state s) (inputs i) = Zmod.unsigned (N.v23759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23759 s i)) at 1.
  unfold R.v23759, N.v23759.
  rewrite ?node_23752.
  rewrite ?node_23753.
  rewrite ?node_23754.
  rewrite ?node_23758.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23760 (s : N.State) (i : N.Inputs) :
  R.v23760 (state s) (inputs i) = Zmod.unsigned (N.v23760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23760 s i)) at 1.
  unfold R.v23760, N.v23760.
  unfold R.v6, N.v6.
  rewrite ?node_23759.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23761 (s : N.State) (i : N.Inputs) :
  R.v23761 (state s) (inputs i) = Zmod.unsigned (N.v23761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23761 s i)) at 1.
  unfold R.v23761, N.v23761.
  rewrite ?node_8729.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23762 (s : N.State) (i : N.Inputs) :
  R.v23762 (state s) (inputs i) = Zmod.unsigned (N.v23762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23762 s i)) at 1.
  unfold R.v23762, N.v23762.
  unfold R.v6, N.v6.
  rewrite ?node_8862.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23763 (s : N.State) (i : N.Inputs) :
  R.v23763 (state s) (inputs i) = Zmod.unsigned (N.v23763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23763 s i)) at 1.
  unfold R.v23763, N.v23763.
  unfold R.v6, N.v6.
  rewrite ?node_8904.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23764 (s : N.State) (i : N.Inputs) :
  R.v23764 (state s) (inputs i) = Zmod.unsigned (N.v23764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23764 s i)) at 1.
  unfold R.v23764, N.v23764.
  rewrite ?node_23761.
  rewrite ?node_23762.
  rewrite ?node_23763.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23765 (s : N.State) (i : N.Inputs) :
  R.v23765 (state s) (inputs i) = Zmod.unsigned (N.v23765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23765 s i)) at 1.
  unfold R.v23765, N.v23765.
  rewrite ?node_23760.
  rewrite ?node_23764.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23766 (s : N.State) (i : N.Inputs) :
  R.v23766 (state s) (inputs i) = Zmod.unsigned (N.v23766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23766 s i)) at 1.
  unfold R.v23766, N.v23766.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23767 (s : N.State) (i : N.Inputs) :
  R.v23767 (state s) (inputs i) = Zmod.unsigned (N.v23767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23767 s i)) at 1.
  unfold R.v23767, N.v23767.
  unfold R.v16463, N.v16463.
  rewrite !state_r804_nr_5F804.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r804_nr_5F804 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23768 (s : N.State) (i : N.Inputs) :
  R.v23768 (state s) (inputs i) = Zmod.unsigned (N.v23768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23768 s i)) at 1.
  unfold R.v23768, N.v23768.
  unfold R.v6, N.v6.
  rewrite !state_r803_nr_5F803.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r803_nr_5F803 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23769 (s : N.State) (i : N.Inputs) :
  R.v23769 (state s) (inputs i) = Zmod.unsigned (N.v23769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23769 s i)) at 1.
  unfold R.v23769, N.v23769.
  unfold R.v6, N.v6.
  rewrite !state_r802_nr_5F802.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r802_nr_5F802 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23770 (s : N.State) (i : N.Inputs) :
  R.v23770 (state s) (inputs i) = Zmod.unsigned (N.v23770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23770 s i)) at 1.
  unfold R.v23770, N.v23770.
  rewrite ?node_23768.
  rewrite ?node_23769.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23771 (s : N.State) (i : N.Inputs) :
  R.v23771 (state s) (inputs i) = Zmod.unsigned (N.v23771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23771 s i)) at 1.
  unfold R.v23771, N.v23771.
  unfold R.v16484, N.v16484.
  rewrite ?node_23770.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23772 (s : N.State) (i : N.Inputs) :
  R.v23772 (state s) (inputs i) = Zmod.unsigned (N.v23772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23772 s i)) at 1.
  unfold R.v23772, N.v23772.
  rewrite ?node_23767.
  rewrite ?node_23771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23773 (s : N.State) (i : N.Inputs) :
  R.v23773 (state s) (inputs i) = Zmod.unsigned (N.v23773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23773 s i)) at 1.
  unfold R.v23773, N.v23773.
  unfold R.v6, N.v6.
  rewrite ?node_23772.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23774 (s : N.State) (i : N.Inputs) :
  R.v23774 (state s) (inputs i) = Zmod.unsigned (N.v23774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23774 s i)) at 1.
  unfold R.v23774, N.v23774.
  rewrite ?node_8724.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23775 (s : N.State) (i : N.Inputs) :
  R.v23775 (state s) (inputs i) = Zmod.unsigned (N.v23775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23775 s i)) at 1.
  unfold R.v23775, N.v23775.
  unfold R.v6, N.v6.
  rewrite ?node_8862.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23776 (s : N.State) (i : N.Inputs) :
  R.v23776 (state s) (inputs i) = Zmod.unsigned (N.v23776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23776 s i)) at 1.
  unfold R.v23776, N.v23776.
  rewrite ?node_23774.
  rewrite ?node_23775.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23777 (s : N.State) (i : N.Inputs) :
  R.v23777 (state s) (inputs i) = Zmod.unsigned (N.v23777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23777 s i)) at 1.
  unfold R.v23777, N.v23777.
  rewrite ?node_23773.
  rewrite ?node_23776.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23778 (s : N.State) (i : N.Inputs) :
  R.v23778 (state s) (inputs i) = Zmod.unsigned (N.v23778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23778 s i)) at 1.
  unfold R.v23778, N.v23778.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23779 (s : N.State) (i : N.Inputs) :
  R.v23779 (state s) (inputs i) = Zmod.unsigned (N.v23779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23779 s i)) at 1.
  unfold R.v23779, N.v23779.
  rewrite ?node_8728.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23780 (s : N.State) (i : N.Inputs) :
  R.v23780 (state s) (inputs i) = Zmod.unsigned (N.v23780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23780 s i)) at 1.
  unfold R.v23780, N.v23780.
  unfold R.v6, N.v6.
  rewrite !state_r805_nr_5F805.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r805_nr_5F805 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23781 (s : N.State) (i : N.Inputs) :
  R.v23781 (state s) (inputs i) = Zmod.unsigned (N.v23781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23781 s i)) at 1.
  unfold R.v23781, N.v23781.
  unfold R.v6, N.v6.
  rewrite ?node_8724.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23782 (s : N.State) (i : N.Inputs) :
  R.v23782 (state s) (inputs i) = Zmod.unsigned (N.v23782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23782 s i)) at 1.
  unfold R.v23782, N.v23782.
  rewrite ?node_23780.
  rewrite ?node_23781.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23783 (s : N.State) (i : N.Inputs) :
  R.v23783 (state s) (inputs i) = Zmod.unsigned (N.v23783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23783 s i)) at 1.
  unfold R.v23783, N.v23783.
  unfold R.v16484, N.v16484.
  rewrite ?node_23782.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23784 (s : N.State) (i : N.Inputs) :
  R.v23784 (state s) (inputs i) = Zmod.unsigned (N.v23784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23784 s i)) at 1.
  unfold R.v23784, N.v23784.
  rewrite ?node_23779.
  rewrite ?node_23783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23785 (s : N.State) (i : N.Inputs) :
  R.v23785 (state s) (inputs i) = Zmod.unsigned (N.v23785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23785 s i)) at 1.
  unfold R.v23785, N.v23785.
  unfold R.v6, N.v6.
  rewrite ?node_23784.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23786 (s : N.State) (i : N.Inputs) :
  R.v23786 (state s) (inputs i) = Zmod.unsigned (N.v23786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23786 s i)) at 1.
  unfold R.v23786, N.v23786.
  rewrite ?node_8729.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23787 (s : N.State) (i : N.Inputs) :
  R.v23787 (state s) (inputs i) = Zmod.unsigned (N.v23787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23787 s i)) at 1.
  unfold R.v23787, N.v23787.
  unfold R.v6, N.v6.
  rewrite ?node_8904.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23788 (s : N.State) (i : N.Inputs) :
  R.v23788 (state s) (inputs i) = Zmod.unsigned (N.v23788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23788 s i)) at 1.
  unfold R.v23788, N.v23788.
  rewrite ?node_23786.
  rewrite ?node_23787.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23789 (s : N.State) (i : N.Inputs) :
  R.v23789 (state s) (inputs i) = Zmod.unsigned (N.v23789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23789 s i)) at 1.
  unfold R.v23789, N.v23789.
  rewrite ?node_23785.
  rewrite ?node_23788.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23790 (s : N.State) (i : N.Inputs) :
  R.v23790 (state s) (inputs i) = Zmod.unsigned (N.v23790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23790 s i)) at 1.
  unfold R.v23790, N.v23790.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23791 (s : N.State) (i : N.Inputs) :
  R.v23791 (state s) (inputs i) = Zmod.unsigned (N.v23791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23791 s i)) at 1.
  unfold R.v23791, N.v23791.
  rewrite ?node_8736.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23792 (s : N.State) (i : N.Inputs) :
  R.v23792 (state s) (inputs i) = Zmod.unsigned (N.v23792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23792 s i)) at 1.
  unfold R.v23792, N.v23792.
  unfold R.v16463, N.v16463.
  rewrite !state_r809_nr_5F809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r809_nr_5F809 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23793 (s : N.State) (i : N.Inputs) :
  R.v23793 (state s) (inputs i) = Zmod.unsigned (N.v23793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23793 s i)) at 1.
  unfold R.v23793, N.v23793.
  unfold R.v16463, N.v16463.
  rewrite !state_r808_nr_5F808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r808_nr_5F808 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23794 (s : N.State) (i : N.Inputs) :
  R.v23794 (state s) (inputs i) = Zmod.unsigned (N.v23794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23794 s i)) at 1.
  unfold R.v23794, N.v23794.
  unfold R.v6, N.v6.
  rewrite !state_r807_nr_5F807.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r807_nr_5F807 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23795 (s : N.State) (i : N.Inputs) :
  R.v23795 (state s) (inputs i) = Zmod.unsigned (N.v23795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23795 s i)) at 1.
  unfold R.v23795, N.v23795.
  unfold R.v6, N.v6.
  rewrite !state_r806_nr_5F806.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r806_nr_5F806 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23796 (s : N.State) (i : N.Inputs) :
  R.v23796 (state s) (inputs i) = Zmod.unsigned (N.v23796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23796 s i)) at 1.
  unfold R.v23796, N.v23796.
  rewrite ?node_23794.
  rewrite ?node_23795.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23797 (s : N.State) (i : N.Inputs) :
  R.v23797 (state s) (inputs i) = Zmod.unsigned (N.v23797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23797 s i)) at 1.
  unfold R.v23797, N.v23797.
  unfold R.v16484, N.v16484.
  rewrite ?node_23796.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23798 (s : N.State) (i : N.Inputs) :
  R.v23798 (state s) (inputs i) = Zmod.unsigned (N.v23798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23798 s i)) at 1.
  unfold R.v23798, N.v23798.
  rewrite ?node_23791.
  rewrite ?node_23792.
  rewrite ?node_23793.
  rewrite ?node_23797.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23799 (s : N.State) (i : N.Inputs) :
  R.v23799 (state s) (inputs i) = Zmod.unsigned (N.v23799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23799 s i)) at 1.
  unfold R.v23799, N.v23799.
  unfold R.v6, N.v6.
  rewrite ?node_23798.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23800 (s : N.State) (i : N.Inputs) :
  R.v23800 (state s) (inputs i) = Zmod.unsigned (N.v23800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23800 s i)) at 1.
  unfold R.v23800, N.v23800.
  rewrite ?node_8737.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23801 (s : N.State) (i : N.Inputs) :
  R.v23801 (state s) (inputs i) = Zmod.unsigned (N.v23801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23801 s i)) at 1.
  unfold R.v23801, N.v23801.
  unfold R.v6, N.v6.
  rewrite ?node_8870.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23802 (s : N.State) (i : N.Inputs) :
  R.v23802 (state s) (inputs i) = Zmod.unsigned (N.v23802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23802 s i)) at 1.
  unfold R.v23802, N.v23802.
  unfold R.v6, N.v6.
  rewrite ?node_8908.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23803 (s : N.State) (i : N.Inputs) :
  R.v23803 (state s) (inputs i) = Zmod.unsigned (N.v23803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23803 s i)) at 1.
  unfold R.v23803, N.v23803.
  rewrite ?node_23800.
  rewrite ?node_23801.
  rewrite ?node_23802.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23804 (s : N.State) (i : N.Inputs) :
  R.v23804 (state s) (inputs i) = Zmod.unsigned (N.v23804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23804 s i)) at 1.
  unfold R.v23804, N.v23804.
  rewrite ?node_23799.
  rewrite ?node_23803.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23805 (s : N.State) (i : N.Inputs) :
  R.v23805 (state s) (inputs i) = Zmod.unsigned (N.v23805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23805 s i)) at 1.
  unfold R.v23805, N.v23805.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23806 (s : N.State) (i : N.Inputs) :
  R.v23806 (state s) (inputs i) = Zmod.unsigned (N.v23806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23806 s i)) at 1.
  unfold R.v23806, N.v23806.
  unfold R.v16463, N.v16463.
  rewrite !state_r808_nr_5F808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r808_nr_5F808 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23807 (s : N.State) (i : N.Inputs) :
  R.v23807 (state s) (inputs i) = Zmod.unsigned (N.v23807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23807 s i)) at 1.
  unfold R.v23807, N.v23807.
  unfold R.v6, N.v6.
  rewrite !state_r807_nr_5F807.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r807_nr_5F807 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23808 (s : N.State) (i : N.Inputs) :
  R.v23808 (state s) (inputs i) = Zmod.unsigned (N.v23808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23808 s i)) at 1.
  unfold R.v23808, N.v23808.
  unfold R.v6, N.v6.
  rewrite !state_r806_nr_5F806.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r806_nr_5F806 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23809 (s : N.State) (i : N.Inputs) :
  R.v23809 (state s) (inputs i) = Zmod.unsigned (N.v23809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23809 s i)) at 1.
  unfold R.v23809, N.v23809.
  rewrite ?node_23807.
  rewrite ?node_23808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23810 (s : N.State) (i : N.Inputs) :
  R.v23810 (state s) (inputs i) = Zmod.unsigned (N.v23810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23810 s i)) at 1.
  unfold R.v23810, N.v23810.
  unfold R.v16484, N.v16484.
  rewrite ?node_23809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23811 (s : N.State) (i : N.Inputs) :
  R.v23811 (state s) (inputs i) = Zmod.unsigned (N.v23811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23811 s i)) at 1.
  unfold R.v23811, N.v23811.
  rewrite ?node_23806.
  rewrite ?node_23810.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23812 (s : N.State) (i : N.Inputs) :
  R.v23812 (state s) (inputs i) = Zmod.unsigned (N.v23812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23812 s i)) at 1.
  unfold R.v23812, N.v23812.
  unfold R.v6, N.v6.
  rewrite ?node_23811.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23813 (s : N.State) (i : N.Inputs) :
  R.v23813 (state s) (inputs i) = Zmod.unsigned (N.v23813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23813 s i)) at 1.
  unfold R.v23813, N.v23813.
  rewrite ?node_8732.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23814 (s : N.State) (i : N.Inputs) :
  R.v23814 (state s) (inputs i) = Zmod.unsigned (N.v23814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23814 s i)) at 1.
  unfold R.v23814, N.v23814.
  unfold R.v6, N.v6.
  rewrite ?node_8870.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23815 (s : N.State) (i : N.Inputs) :
  R.v23815 (state s) (inputs i) = Zmod.unsigned (N.v23815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23815 s i)) at 1.
  unfold R.v23815, N.v23815.
  rewrite ?node_23813.
  rewrite ?node_23814.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23816 (s : N.State) (i : N.Inputs) :
  R.v23816 (state s) (inputs i) = Zmod.unsigned (N.v23816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23816 s i)) at 1.
  unfold R.v23816, N.v23816.
  rewrite ?node_23812.
  rewrite ?node_23815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23817 (s : N.State) (i : N.Inputs) :
  R.v23817 (state s) (inputs i) = Zmod.unsigned (N.v23817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23817 s i)) at 1.
  unfold R.v23817, N.v23817.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23818 (s : N.State) (i : N.Inputs) :
  R.v23818 (state s) (inputs i) = Zmod.unsigned (N.v23818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23818 s i)) at 1.
  unfold R.v23818, N.v23818.
  rewrite ?node_8736.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23819 (s : N.State) (i : N.Inputs) :
  R.v23819 (state s) (inputs i) = Zmod.unsigned (N.v23819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23819 s i)) at 1.
  unfold R.v23819, N.v23819.
  unfold R.v6, N.v6.
  rewrite !state_r809_nr_5F809.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r809_nr_5F809 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23820 (s : N.State) (i : N.Inputs) :
  R.v23820 (state s) (inputs i) = Zmod.unsigned (N.v23820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23820 s i)) at 1.
  unfold R.v23820, N.v23820.
  unfold R.v6, N.v6.
  rewrite ?node_8732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23821 (s : N.State) (i : N.Inputs) :
  R.v23821 (state s) (inputs i) = Zmod.unsigned (N.v23821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23821 s i)) at 1.
  unfold R.v23821, N.v23821.
  rewrite ?node_23819.
  rewrite ?node_23820.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23822 (s : N.State) (i : N.Inputs) :
  R.v23822 (state s) (inputs i) = Zmod.unsigned (N.v23822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23822 s i)) at 1.
  unfold R.v23822, N.v23822.
  unfold R.v16484, N.v16484.
  rewrite ?node_23821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23823 (s : N.State) (i : N.Inputs) :
  R.v23823 (state s) (inputs i) = Zmod.unsigned (N.v23823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23823 s i)) at 1.
  unfold R.v23823, N.v23823.
  rewrite ?node_23818.
  rewrite ?node_23822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23824 (s : N.State) (i : N.Inputs) :
  R.v23824 (state s) (inputs i) = Zmod.unsigned (N.v23824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23824 s i)) at 1.
  unfold R.v23824, N.v23824.
  unfold R.v6, N.v6.
  rewrite ?node_23823.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23825 (s : N.State) (i : N.Inputs) :
  R.v23825 (state s) (inputs i) = Zmod.unsigned (N.v23825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23825 s i)) at 1.
  unfold R.v23825, N.v23825.
  rewrite ?node_8737.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23826 (s : N.State) (i : N.Inputs) :
  R.v23826 (state s) (inputs i) = Zmod.unsigned (N.v23826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23826 s i)) at 1.
  unfold R.v23826, N.v23826.
  unfold R.v6, N.v6.
  rewrite ?node_8908.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23827 (s : N.State) (i : N.Inputs) :
  R.v23827 (state s) (inputs i) = Zmod.unsigned (N.v23827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23827 s i)) at 1.
  unfold R.v23827, N.v23827.
  rewrite ?node_23825.
  rewrite ?node_23826.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23828 (s : N.State) (i : N.Inputs) :
  R.v23828 (state s) (inputs i) = Zmod.unsigned (N.v23828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23828 s i)) at 1.
  unfold R.v23828, N.v23828.
  rewrite ?node_23824.
  rewrite ?node_23827.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23829 (s : N.State) (i : N.Inputs) :
  R.v23829 (state s) (inputs i) = Zmod.unsigned (N.v23829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23829 s i)) at 1.
  unfold R.v23829, N.v23829.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23830 (s : N.State) (i : N.Inputs) :
  R.v23830 (state s) (inputs i) = Zmod.unsigned (N.v23830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23830 s i)) at 1.
  unfold R.v23830, N.v23830.
  rewrite ?node_8820.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23831 (s : N.State) (i : N.Inputs) :
  R.v23831 (state s) (inputs i) = Zmod.unsigned (N.v23831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23831 s i)) at 1.
  unfold R.v23831, N.v23831.
  unfold R.v16463, N.v16463.
  rewrite !state_r813_nr_5F813.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r813_nr_5F813 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23832 (s : N.State) (i : N.Inputs) :
  R.v23832 (state s) (inputs i) = Zmod.unsigned (N.v23832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23832 s i)) at 1.
  unfold R.v23832, N.v23832.
  unfold R.v16463, N.v16463.
  rewrite !state_r812_nr_5F812.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r812_nr_5F812 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23833 (s : N.State) (i : N.Inputs) :
  R.v23833 (state s) (inputs i) = Zmod.unsigned (N.v23833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23833 s i)) at 1.
  unfold R.v23833, N.v23833.
  unfold R.v6, N.v6.
  rewrite !state_r811_nr_5F811.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r811_nr_5F811 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23834 (s : N.State) (i : N.Inputs) :
  R.v23834 (state s) (inputs i) = Zmod.unsigned (N.v23834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23834 s i)) at 1.
  unfold R.v23834, N.v23834.
  unfold R.v6, N.v6.
  rewrite !state_r810_nr_5F810.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r810_nr_5F810 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23835 (s : N.State) (i : N.Inputs) :
  R.v23835 (state s) (inputs i) = Zmod.unsigned (N.v23835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23835 s i)) at 1.
  unfold R.v23835, N.v23835.
  rewrite ?node_23833.
  rewrite ?node_23834.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23836 (s : N.State) (i : N.Inputs) :
  R.v23836 (state s) (inputs i) = Zmod.unsigned (N.v23836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23836 s i)) at 1.
  unfold R.v23836, N.v23836.
  unfold R.v16484, N.v16484.
  rewrite ?node_23835.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23837 (s : N.State) (i : N.Inputs) :
  R.v23837 (state s) (inputs i) = Zmod.unsigned (N.v23837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23837 s i)) at 1.
  unfold R.v23837, N.v23837.
  rewrite ?node_23830.
  rewrite ?node_23831.
  rewrite ?node_23832.
  rewrite ?node_23836.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23838 (s : N.State) (i : N.Inputs) :
  R.v23838 (state s) (inputs i) = Zmod.unsigned (N.v23838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23838 s i)) at 1.
  unfold R.v23838, N.v23838.
  unfold R.v6, N.v6.
  rewrite ?node_23837.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23839 (s : N.State) (i : N.Inputs) :
  R.v23839 (state s) (inputs i) = Zmod.unsigned (N.v23839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23839 s i)) at 1.
  unfold R.v23839, N.v23839.
  rewrite ?node_8821.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23840 (s : N.State) (i : N.Inputs) :
  R.v23840 (state s) (inputs i) = Zmod.unsigned (N.v23840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23840 s i)) at 1.
  unfold R.v23840, N.v23840.
  unfold R.v6, N.v6.
  rewrite ?node_8957.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23841 (s : N.State) (i : N.Inputs) :
  R.v23841 (state s) (inputs i) = Zmod.unsigned (N.v23841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23841 s i)) at 1.
  unfold R.v23841, N.v23841.
  unfold R.v6, N.v6.
  rewrite ?node_9018.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23842 (s : N.State) (i : N.Inputs) :
  R.v23842 (state s) (inputs i) = Zmod.unsigned (N.v23842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23842 s i)) at 1.
  unfold R.v23842, N.v23842.
  rewrite ?node_23839.
  rewrite ?node_23840.
  rewrite ?node_23841.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23843 (s : N.State) (i : N.Inputs) :
  R.v23843 (state s) (inputs i) = Zmod.unsigned (N.v23843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23843 s i)) at 1.
  unfold R.v23843, N.v23843.
  rewrite ?node_23838.
  rewrite ?node_23842.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23844 (s : N.State) (i : N.Inputs) :
  R.v23844 (state s) (inputs i) = Zmod.unsigned (N.v23844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23844 s i)) at 1.
  unfold R.v23844, N.v23844.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23845 (s : N.State) (i : N.Inputs) :
  R.v23845 (state s) (inputs i) = Zmod.unsigned (N.v23845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23845 s i)) at 1.
  unfold R.v23845, N.v23845.
  unfold R.v16463, N.v16463.
  rewrite !state_r812_nr_5F812.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r812_nr_5F812 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23846 (s : N.State) (i : N.Inputs) :
  R.v23846 (state s) (inputs i) = Zmod.unsigned (N.v23846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23846 s i)) at 1.
  unfold R.v23846, N.v23846.
  unfold R.v6, N.v6.
  rewrite !state_r811_nr_5F811.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r811_nr_5F811 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23847 (s : N.State) (i : N.Inputs) :
  R.v23847 (state s) (inputs i) = Zmod.unsigned (N.v23847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23847 s i)) at 1.
  unfold R.v23847, N.v23847.
  unfold R.v6, N.v6.
  rewrite !state_r810_nr_5F810.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r810_nr_5F810 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23848 (s : N.State) (i : N.Inputs) :
  R.v23848 (state s) (inputs i) = Zmod.unsigned (N.v23848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23848 s i)) at 1.
  unfold R.v23848, N.v23848.
  rewrite ?node_23846.
  rewrite ?node_23847.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23849 (s : N.State) (i : N.Inputs) :
  R.v23849 (state s) (inputs i) = Zmod.unsigned (N.v23849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23849 s i)) at 1.
  unfold R.v23849, N.v23849.
  unfold R.v16484, N.v16484.
  rewrite ?node_23848.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23850 (s : N.State) (i : N.Inputs) :
  R.v23850 (state s) (inputs i) = Zmod.unsigned (N.v23850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23850 s i)) at 1.
  unfold R.v23850, N.v23850.
  rewrite ?node_23845.
  rewrite ?node_23849.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23851 (s : N.State) (i : N.Inputs) :
  R.v23851 (state s) (inputs i) = Zmod.unsigned (N.v23851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23851 s i)) at 1.
  unfold R.v23851, N.v23851.
  unfold R.v6, N.v6.
  rewrite ?node_23850.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23852 (s : N.State) (i : N.Inputs) :
  R.v23852 (state s) (inputs i) = Zmod.unsigned (N.v23852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23852 s i)) at 1.
  unfold R.v23852, N.v23852.
  rewrite ?node_8816.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23853 (s : N.State) (i : N.Inputs) :
  R.v23853 (state s) (inputs i) = Zmod.unsigned (N.v23853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23853 s i)) at 1.
  unfold R.v23853, N.v23853.
  unfold R.v6, N.v6.
  rewrite ?node_8957.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23854 (s : N.State) (i : N.Inputs) :
  R.v23854 (state s) (inputs i) = Zmod.unsigned (N.v23854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23854 s i)) at 1.
  unfold R.v23854, N.v23854.
  rewrite ?node_23852.
  rewrite ?node_23853.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23855 (s : N.State) (i : N.Inputs) :
  R.v23855 (state s) (inputs i) = Zmod.unsigned (N.v23855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23855 s i)) at 1.
  unfold R.v23855, N.v23855.
  rewrite ?node_23851.
  rewrite ?node_23854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23856 (s : N.State) (i : N.Inputs) :
  R.v23856 (state s) (inputs i) = Zmod.unsigned (N.v23856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23856 s i)) at 1.
  unfold R.v23856, N.v23856.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23857 (s : N.State) (i : N.Inputs) :
  R.v23857 (state s) (inputs i) = Zmod.unsigned (N.v23857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23857 s i)) at 1.
  unfold R.v23857, N.v23857.
  rewrite ?node_8820.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23858 (s : N.State) (i : N.Inputs) :
  R.v23858 (state s) (inputs i) = Zmod.unsigned (N.v23858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23858 s i)) at 1.
  unfold R.v23858, N.v23858.
  unfold R.v6, N.v6.
  rewrite !state_r813_nr_5F813.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r813_nr_5F813 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23859 (s : N.State) (i : N.Inputs) :
  R.v23859 (state s) (inputs i) = Zmod.unsigned (N.v23859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23859 s i)) at 1.
  unfold R.v23859, N.v23859.
  unfold R.v6, N.v6.
  rewrite ?node_8816.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23860 (s : N.State) (i : N.Inputs) :
  R.v23860 (state s) (inputs i) = Zmod.unsigned (N.v23860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23860 s i)) at 1.
  unfold R.v23860, N.v23860.
  rewrite ?node_23858.
  rewrite ?node_23859.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23861 (s : N.State) (i : N.Inputs) :
  R.v23861 (state s) (inputs i) = Zmod.unsigned (N.v23861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23861 s i)) at 1.
  unfold R.v23861, N.v23861.
  unfold R.v16484, N.v16484.
  rewrite ?node_23860.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23862 (s : N.State) (i : N.Inputs) :
  R.v23862 (state s) (inputs i) = Zmod.unsigned (N.v23862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23862 s i)) at 1.
  unfold R.v23862, N.v23862.
  rewrite ?node_23857.
  rewrite ?node_23861.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23863 (s : N.State) (i : N.Inputs) :
  R.v23863 (state s) (inputs i) = Zmod.unsigned (N.v23863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23863 s i)) at 1.
  unfold R.v23863, N.v23863.
  unfold R.v6, N.v6.
  rewrite ?node_23862.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23864 (s : N.State) (i : N.Inputs) :
  R.v23864 (state s) (inputs i) = Zmod.unsigned (N.v23864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23864 s i)) at 1.
  unfold R.v23864, N.v23864.
  rewrite ?node_8821.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23865 (s : N.State) (i : N.Inputs) :
  R.v23865 (state s) (inputs i) = Zmod.unsigned (N.v23865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23865 s i)) at 1.
  unfold R.v23865, N.v23865.
  unfold R.v6, N.v6.
  rewrite ?node_9018.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23866 (s : N.State) (i : N.Inputs) :
  R.v23866 (state s) (inputs i) = Zmod.unsigned (N.v23866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23866 s i)) at 1.
  unfold R.v23866, N.v23866.
  rewrite ?node_23864.
  rewrite ?node_23865.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23867 (s : N.State) (i : N.Inputs) :
  R.v23867 (state s) (inputs i) = Zmod.unsigned (N.v23867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23867 s i)) at 1.
  unfold R.v23867, N.v23867.
  rewrite ?node_23863.
  rewrite ?node_23866.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23868 (s : N.State) (i : N.Inputs) :
  R.v23868 (state s) (inputs i) = Zmod.unsigned (N.v23868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23868 s i)) at 1.
  unfold R.v23868, N.v23868.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23869 (s : N.State) (i : N.Inputs) :
  R.v23869 (state s) (inputs i) = Zmod.unsigned (N.v23869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23869 s i)) at 1.
  unfold R.v23869, N.v23869.
  rewrite ?node_8827.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23870 (s : N.State) (i : N.Inputs) :
  R.v23870 (state s) (inputs i) = Zmod.unsigned (N.v23870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23870 s i)) at 1.
  unfold R.v23870, N.v23870.
  unfold R.v16463, N.v16463.
  rewrite !state_r817_nr_5F817.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r817_nr_5F817 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23871 (s : N.State) (i : N.Inputs) :
  R.v23871 (state s) (inputs i) = Zmod.unsigned (N.v23871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23871 s i)) at 1.
  unfold R.v23871, N.v23871.
  unfold R.v16463, N.v16463.
  rewrite !state_r816_nr_5F816.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r816_nr_5F816 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23872 (s : N.State) (i : N.Inputs) :
  R.v23872 (state s) (inputs i) = Zmod.unsigned (N.v23872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23872 s i)) at 1.
  unfold R.v23872, N.v23872.
  unfold R.v6, N.v6.
  rewrite !state_r815_nr_5F815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r815_nr_5F815 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23873 (s : N.State) (i : N.Inputs) :
  R.v23873 (state s) (inputs i) = Zmod.unsigned (N.v23873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23873 s i)) at 1.
  unfold R.v23873, N.v23873.
  unfold R.v6, N.v6.
  rewrite !state_r814_nr_5F814.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r814_nr_5F814 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23874 (s : N.State) (i : N.Inputs) :
  R.v23874 (state s) (inputs i) = Zmod.unsigned (N.v23874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23874 s i)) at 1.
  unfold R.v23874, N.v23874.
  rewrite ?node_23872.
  rewrite ?node_23873.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23875 (s : N.State) (i : N.Inputs) :
  R.v23875 (state s) (inputs i) = Zmod.unsigned (N.v23875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23875 s i)) at 1.
  unfold R.v23875, N.v23875.
  unfold R.v16484, N.v16484.
  rewrite ?node_23874.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23876 (s : N.State) (i : N.Inputs) :
  R.v23876 (state s) (inputs i) = Zmod.unsigned (N.v23876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23876 s i)) at 1.
  unfold R.v23876, N.v23876.
  rewrite ?node_23869.
  rewrite ?node_23870.
  rewrite ?node_23871.
  rewrite ?node_23875.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23877 (s : N.State) (i : N.Inputs) :
  R.v23877 (state s) (inputs i) = Zmod.unsigned (N.v23877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23877 s i)) at 1.
  unfold R.v23877, N.v23877.
  unfold R.v6, N.v6.
  rewrite ?node_23876.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23878 (s : N.State) (i : N.Inputs) :
  R.v23878 (state s) (inputs i) = Zmod.unsigned (N.v23878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23878 s i)) at 1.
  unfold R.v23878, N.v23878.
  rewrite ?node_8828.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23879 (s : N.State) (i : N.Inputs) :
  R.v23879 (state s) (inputs i) = Zmod.unsigned (N.v23879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23879 s i)) at 1.
  unfold R.v23879, N.v23879.
  unfold R.v6, N.v6.
  rewrite ?node_8964.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23880 (s : N.State) (i : N.Inputs) :
  R.v23880 (state s) (inputs i) = Zmod.unsigned (N.v23880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23880 s i)) at 1.
  unfold R.v23880, N.v23880.
  unfold R.v6, N.v6.
  rewrite ?node_9021.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23881 (s : N.State) (i : N.Inputs) :
  R.v23881 (state s) (inputs i) = Zmod.unsigned (N.v23881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23881 s i)) at 1.
  unfold R.v23881, N.v23881.
  rewrite ?node_23878.
  rewrite ?node_23879.
  rewrite ?node_23880.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23882 (s : N.State) (i : N.Inputs) :
  R.v23882 (state s) (inputs i) = Zmod.unsigned (N.v23882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23882 s i)) at 1.
  unfold R.v23882, N.v23882.
  rewrite ?node_23877.
  rewrite ?node_23881.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23883 (s : N.State) (i : N.Inputs) :
  R.v23883 (state s) (inputs i) = Zmod.unsigned (N.v23883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23883 s i)) at 1.
  unfold R.v23883, N.v23883.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23884 (s : N.State) (i : N.Inputs) :
  R.v23884 (state s) (inputs i) = Zmod.unsigned (N.v23884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23884 s i)) at 1.
  unfold R.v23884, N.v23884.
  unfold R.v16463, N.v16463.
  rewrite !state_r816_nr_5F816.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r816_nr_5F816 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23885 (s : N.State) (i : N.Inputs) :
  R.v23885 (state s) (inputs i) = Zmod.unsigned (N.v23885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23885 s i)) at 1.
  unfold R.v23885, N.v23885.
  unfold R.v6, N.v6.
  rewrite !state_r815_nr_5F815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r815_nr_5F815 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23886 (s : N.State) (i : N.Inputs) :
  R.v23886 (state s) (inputs i) = Zmod.unsigned (N.v23886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23886 s i)) at 1.
  unfold R.v23886, N.v23886.
  unfold R.v6, N.v6.
  rewrite !state_r814_nr_5F814.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r814_nr_5F814 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23887 (s : N.State) (i : N.Inputs) :
  R.v23887 (state s) (inputs i) = Zmod.unsigned (N.v23887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23887 s i)) at 1.
  unfold R.v23887, N.v23887.
  rewrite ?node_23885.
  rewrite ?node_23886.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23888 (s : N.State) (i : N.Inputs) :
  R.v23888 (state s) (inputs i) = Zmod.unsigned (N.v23888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23888 s i)) at 1.
  unfold R.v23888, N.v23888.
  unfold R.v16484, N.v16484.
  rewrite ?node_23887.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23889 (s : N.State) (i : N.Inputs) :
  R.v23889 (state s) (inputs i) = Zmod.unsigned (N.v23889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23889 s i)) at 1.
  unfold R.v23889, N.v23889.
  rewrite ?node_23884.
  rewrite ?node_23888.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23890 (s : N.State) (i : N.Inputs) :
  R.v23890 (state s) (inputs i) = Zmod.unsigned (N.v23890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23890 s i)) at 1.
  unfold R.v23890, N.v23890.
  unfold R.v6, N.v6.
  rewrite ?node_23889.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23891 (s : N.State) (i : N.Inputs) :
  R.v23891 (state s) (inputs i) = Zmod.unsigned (N.v23891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23891 s i)) at 1.
  unfold R.v23891, N.v23891.
  rewrite ?node_8823.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23892 (s : N.State) (i : N.Inputs) :
  R.v23892 (state s) (inputs i) = Zmod.unsigned (N.v23892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23892 s i)) at 1.
  unfold R.v23892, N.v23892.
  unfold R.v6, N.v6.
  rewrite ?node_8964.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23893 (s : N.State) (i : N.Inputs) :
  R.v23893 (state s) (inputs i) = Zmod.unsigned (N.v23893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23893 s i)) at 1.
  unfold R.v23893, N.v23893.
  rewrite ?node_23891.
  rewrite ?node_23892.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23894 (s : N.State) (i : N.Inputs) :
  R.v23894 (state s) (inputs i) = Zmod.unsigned (N.v23894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23894 s i)) at 1.
  unfold R.v23894, N.v23894.
  rewrite ?node_23890.
  rewrite ?node_23893.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23895 (s : N.State) (i : N.Inputs) :
  R.v23895 (state s) (inputs i) = Zmod.unsigned (N.v23895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23895 s i)) at 1.
  unfold R.v23895, N.v23895.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23896 (s : N.State) (i : N.Inputs) :
  R.v23896 (state s) (inputs i) = Zmod.unsigned (N.v23896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23896 s i)) at 1.
  unfold R.v23896, N.v23896.
  rewrite ?node_8827.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23897 (s : N.State) (i : N.Inputs) :
  R.v23897 (state s) (inputs i) = Zmod.unsigned (N.v23897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23897 s i)) at 1.
  unfold R.v23897, N.v23897.
  unfold R.v6, N.v6.
  rewrite !state_r817_nr_5F817.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r817_nr_5F817 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23898 (s : N.State) (i : N.Inputs) :
  R.v23898 (state s) (inputs i) = Zmod.unsigned (N.v23898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23898 s i)) at 1.
  unfold R.v23898, N.v23898.
  unfold R.v6, N.v6.
  rewrite ?node_8823.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23899 (s : N.State) (i : N.Inputs) :
  R.v23899 (state s) (inputs i) = Zmod.unsigned (N.v23899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23899 s i)) at 1.
  unfold R.v23899, N.v23899.
  rewrite ?node_23897.
  rewrite ?node_23898.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23900 (s : N.State) (i : N.Inputs) :
  R.v23900 (state s) (inputs i) = Zmod.unsigned (N.v23900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23900 s i)) at 1.
  unfold R.v23900, N.v23900.
  unfold R.v16484, N.v16484.
  rewrite ?node_23899.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23901 (s : N.State) (i : N.Inputs) :
  R.v23901 (state s) (inputs i) = Zmod.unsigned (N.v23901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23901 s i)) at 1.
  unfold R.v23901, N.v23901.
  rewrite ?node_23896.
  rewrite ?node_23900.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23902 (s : N.State) (i : N.Inputs) :
  R.v23902 (state s) (inputs i) = Zmod.unsigned (N.v23902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23902 s i)) at 1.
  unfold R.v23902, N.v23902.
  unfold R.v6, N.v6.
  rewrite ?node_23901.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23903 (s : N.State) (i : N.Inputs) :
  R.v23903 (state s) (inputs i) = Zmod.unsigned (N.v23903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23903 s i)) at 1.
  unfold R.v23903, N.v23903.
  rewrite ?node_8828.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23904 (s : N.State) (i : N.Inputs) :
  R.v23904 (state s) (inputs i) = Zmod.unsigned (N.v23904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23904 s i)) at 1.
  unfold R.v23904, N.v23904.
  unfold R.v6, N.v6.
  rewrite ?node_9021.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23905 (s : N.State) (i : N.Inputs) :
  R.v23905 (state s) (inputs i) = Zmod.unsigned (N.v23905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23905 s i)) at 1.
  unfold R.v23905, N.v23905.
  rewrite ?node_23903.
  rewrite ?node_23904.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23906 (s : N.State) (i : N.Inputs) :
  R.v23906 (state s) (inputs i) = Zmod.unsigned (N.v23906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23906 s i)) at 1.
  unfold R.v23906, N.v23906.
  rewrite ?node_23902.
  rewrite ?node_23905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23907 (s : N.State) (i : N.Inputs) :
  R.v23907 (state s) (inputs i) = Zmod.unsigned (N.v23907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23907 s i)) at 1.
  unfold R.v23907, N.v23907.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23908 (s : N.State) (i : N.Inputs) :
  R.v23908 (state s) (inputs i) = Zmod.unsigned (N.v23908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23908 s i)) at 1.
  unfold R.v23908, N.v23908.
  rewrite ?node_8835.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23909 (s : N.State) (i : N.Inputs) :
  R.v23909 (state s) (inputs i) = Zmod.unsigned (N.v23909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23909 s i)) at 1.
  unfold R.v23909, N.v23909.
  unfold R.v16463, N.v16463.
  rewrite !state_r821_nr_5F821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r821_nr_5F821 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23910 (s : N.State) (i : N.Inputs) :
  R.v23910 (state s) (inputs i) = Zmod.unsigned (N.v23910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23910 s i)) at 1.
  unfold R.v23910, N.v23910.
  unfold R.v16463, N.v16463.
  rewrite !state_r820_nr_5F820.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r820_nr_5F820 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23911 (s : N.State) (i : N.Inputs) :
  R.v23911 (state s) (inputs i) = Zmod.unsigned (N.v23911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23911 s i)) at 1.
  unfold R.v23911, N.v23911.
  unfold R.v6, N.v6.
  rewrite !state_r819_nr_5F819.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r819_nr_5F819 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23912 (s : N.State) (i : N.Inputs) :
  R.v23912 (state s) (inputs i) = Zmod.unsigned (N.v23912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23912 s i)) at 1.
  unfold R.v23912, N.v23912.
  unfold R.v6, N.v6.
  rewrite !state_r818_nr_5F818.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r818_nr_5F818 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23913 (s : N.State) (i : N.Inputs) :
  R.v23913 (state s) (inputs i) = Zmod.unsigned (N.v23913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23913 s i)) at 1.
  unfold R.v23913, N.v23913.
  rewrite ?node_23911.
  rewrite ?node_23912.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23914 (s : N.State) (i : N.Inputs) :
  R.v23914 (state s) (inputs i) = Zmod.unsigned (N.v23914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23914 s i)) at 1.
  unfold R.v23914, N.v23914.
  unfold R.v16484, N.v16484.
  rewrite ?node_23913.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23915 (s : N.State) (i : N.Inputs) :
  R.v23915 (state s) (inputs i) = Zmod.unsigned (N.v23915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23915 s i)) at 1.
  unfold R.v23915, N.v23915.
  rewrite ?node_23908.
  rewrite ?node_23909.
  rewrite ?node_23910.
  rewrite ?node_23914.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23916 (s : N.State) (i : N.Inputs) :
  R.v23916 (state s) (inputs i) = Zmod.unsigned (N.v23916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23916 s i)) at 1.
  unfold R.v23916, N.v23916.
  unfold R.v6, N.v6.
  rewrite ?node_23915.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23917 (s : N.State) (i : N.Inputs) :
  R.v23917 (state s) (inputs i) = Zmod.unsigned (N.v23917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23917 s i)) at 1.
  unfold R.v23917, N.v23917.
  rewrite ?node_8836.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23918 (s : N.State) (i : N.Inputs) :
  R.v23918 (state s) (inputs i) = Zmod.unsigned (N.v23918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23918 s i)) at 1.
  unfold R.v23918, N.v23918.
  unfold R.v6, N.v6.
  rewrite ?node_8972.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23919 (s : N.State) (i : N.Inputs) :
  R.v23919 (state s) (inputs i) = Zmod.unsigned (N.v23919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23919 s i)) at 1.
  unfold R.v23919, N.v23919.
  unfold R.v6, N.v6.
  rewrite ?node_9025.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23920 (s : N.State) (i : N.Inputs) :
  R.v23920 (state s) (inputs i) = Zmod.unsigned (N.v23920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23920 s i)) at 1.
  unfold R.v23920, N.v23920.
  rewrite ?node_23917.
  rewrite ?node_23918.
  rewrite ?node_23919.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23921 (s : N.State) (i : N.Inputs) :
  R.v23921 (state s) (inputs i) = Zmod.unsigned (N.v23921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23921 s i)) at 1.
  unfold R.v23921, N.v23921.
  rewrite ?node_23916.
  rewrite ?node_23920.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23922 (s : N.State) (i : N.Inputs) :
  R.v23922 (state s) (inputs i) = Zmod.unsigned (N.v23922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23922 s i)) at 1.
  unfold R.v23922, N.v23922.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23923 (s : N.State) (i : N.Inputs) :
  R.v23923 (state s) (inputs i) = Zmod.unsigned (N.v23923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23923 s i)) at 1.
  unfold R.v23923, N.v23923.
  unfold R.v16463, N.v16463.
  rewrite !state_r820_nr_5F820.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r820_nr_5F820 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23924 (s : N.State) (i : N.Inputs) :
  R.v23924 (state s) (inputs i) = Zmod.unsigned (N.v23924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23924 s i)) at 1.
  unfold R.v23924, N.v23924.
  unfold R.v6, N.v6.
  rewrite !state_r819_nr_5F819.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r819_nr_5F819 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23925 (s : N.State) (i : N.Inputs) :
  R.v23925 (state s) (inputs i) = Zmod.unsigned (N.v23925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23925 s i)) at 1.
  unfold R.v23925, N.v23925.
  unfold R.v6, N.v6.
  rewrite !state_r818_nr_5F818.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r818_nr_5F818 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23926 (s : N.State) (i : N.Inputs) :
  R.v23926 (state s) (inputs i) = Zmod.unsigned (N.v23926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23926 s i)) at 1.
  unfold R.v23926, N.v23926.
  rewrite ?node_23924.
  rewrite ?node_23925.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23927 (s : N.State) (i : N.Inputs) :
  R.v23927 (state s) (inputs i) = Zmod.unsigned (N.v23927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23927 s i)) at 1.
  unfold R.v23927, N.v23927.
  unfold R.v16484, N.v16484.
  rewrite ?node_23926.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23928 (s : N.State) (i : N.Inputs) :
  R.v23928 (state s) (inputs i) = Zmod.unsigned (N.v23928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23928 s i)) at 1.
  unfold R.v23928, N.v23928.
  rewrite ?node_23923.
  rewrite ?node_23927.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23929 (s : N.State) (i : N.Inputs) :
  R.v23929 (state s) (inputs i) = Zmod.unsigned (N.v23929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23929 s i)) at 1.
  unfold R.v23929, N.v23929.
  unfold R.v6, N.v6.
  rewrite ?node_23928.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23930 (s : N.State) (i : N.Inputs) :
  R.v23930 (state s) (inputs i) = Zmod.unsigned (N.v23930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23930 s i)) at 1.
  unfold R.v23930, N.v23930.
  rewrite ?node_8831.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23931 (s : N.State) (i : N.Inputs) :
  R.v23931 (state s) (inputs i) = Zmod.unsigned (N.v23931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23931 s i)) at 1.
  unfold R.v23931, N.v23931.
  unfold R.v6, N.v6.
  rewrite ?node_8972.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23932 (s : N.State) (i : N.Inputs) :
  R.v23932 (state s) (inputs i) = Zmod.unsigned (N.v23932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23932 s i)) at 1.
  unfold R.v23932, N.v23932.
  rewrite ?node_23930.
  rewrite ?node_23931.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23933 (s : N.State) (i : N.Inputs) :
  R.v23933 (state s) (inputs i) = Zmod.unsigned (N.v23933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23933 s i)) at 1.
  unfold R.v23933, N.v23933.
  rewrite ?node_23929.
  rewrite ?node_23932.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23934 (s : N.State) (i : N.Inputs) :
  R.v23934 (state s) (inputs i) = Zmod.unsigned (N.v23934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23934 s i)) at 1.
  unfold R.v23934, N.v23934.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23935 (s : N.State) (i : N.Inputs) :
  R.v23935 (state s) (inputs i) = Zmod.unsigned (N.v23935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23935 s i)) at 1.
  unfold R.v23935, N.v23935.
  rewrite ?node_8835.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23936 (s : N.State) (i : N.Inputs) :
  R.v23936 (state s) (inputs i) = Zmod.unsigned (N.v23936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23936 s i)) at 1.
  unfold R.v23936, N.v23936.
  unfold R.v6, N.v6.
  rewrite !state_r821_nr_5F821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r821_nr_5F821 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23937 (s : N.State) (i : N.Inputs) :
  R.v23937 (state s) (inputs i) = Zmod.unsigned (N.v23937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23937 s i)) at 1.
  unfold R.v23937, N.v23937.
  unfold R.v6, N.v6.
  rewrite ?node_8831.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23938 (s : N.State) (i : N.Inputs) :
  R.v23938 (state s) (inputs i) = Zmod.unsigned (N.v23938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23938 s i)) at 1.
  unfold R.v23938, N.v23938.
  rewrite ?node_23936.
  rewrite ?node_23937.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23939 (s : N.State) (i : N.Inputs) :
  R.v23939 (state s) (inputs i) = Zmod.unsigned (N.v23939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23939 s i)) at 1.
  unfold R.v23939, N.v23939.
  unfold R.v16484, N.v16484.
  rewrite ?node_23938.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23940 (s : N.State) (i : N.Inputs) :
  R.v23940 (state s) (inputs i) = Zmod.unsigned (N.v23940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23940 s i)) at 1.
  unfold R.v23940, N.v23940.
  rewrite ?node_23935.
  rewrite ?node_23939.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23941 (s : N.State) (i : N.Inputs) :
  R.v23941 (state s) (inputs i) = Zmod.unsigned (N.v23941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23941 s i)) at 1.
  unfold R.v23941, N.v23941.
  unfold R.v6, N.v6.
  rewrite ?node_23940.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23942 (s : N.State) (i : N.Inputs) :
  R.v23942 (state s) (inputs i) = Zmod.unsigned (N.v23942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23942 s i)) at 1.
  unfold R.v23942, N.v23942.
  rewrite ?node_8836.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23943 (s : N.State) (i : N.Inputs) :
  R.v23943 (state s) (inputs i) = Zmod.unsigned (N.v23943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23943 s i)) at 1.
  unfold R.v23943, N.v23943.
  unfold R.v6, N.v6.
  rewrite ?node_9025.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23944 (s : N.State) (i : N.Inputs) :
  R.v23944 (state s) (inputs i) = Zmod.unsigned (N.v23944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23944 s i)) at 1.
  unfold R.v23944, N.v23944.
  rewrite ?node_23942.
  rewrite ?node_23943.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23945 (s : N.State) (i : N.Inputs) :
  R.v23945 (state s) (inputs i) = Zmod.unsigned (N.v23945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23945 s i)) at 1.
  unfold R.v23945, N.v23945.
  rewrite ?node_23941.
  rewrite ?node_23944.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23946 (s : N.State) (i : N.Inputs) :
  R.v23946 (state s) (inputs i) = Zmod.unsigned (N.v23946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23946 s i)) at 1.
  unfold R.v23946, N.v23946.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23947 (s : N.State) (i : N.Inputs) :
  R.v23947 (state s) (inputs i) = Zmod.unsigned (N.v23947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23947 s i)) at 1.
  unfold R.v23947, N.v23947.
  rewrite ?node_8843.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23948 (s : N.State) (i : N.Inputs) :
  R.v23948 (state s) (inputs i) = Zmod.unsigned (N.v23948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23948 s i)) at 1.
  unfold R.v23948, N.v23948.
  unfold R.v16463, N.v16463.
  rewrite !state_r825_nr_5F825.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r825_nr_5F825 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23949 (s : N.State) (i : N.Inputs) :
  R.v23949 (state s) (inputs i) = Zmod.unsigned (N.v23949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23949 s i)) at 1.
  unfold R.v23949, N.v23949.
  unfold R.v16463, N.v16463.
  rewrite !state_r824_nr_5F824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r824_nr_5F824 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23950 (s : N.State) (i : N.Inputs) :
  R.v23950 (state s) (inputs i) = Zmod.unsigned (N.v23950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23950 s i)) at 1.
  unfold R.v23950, N.v23950.
  unfold R.v6, N.v6.
  rewrite !state_r823_nr_5F823.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r823_nr_5F823 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23951 (s : N.State) (i : N.Inputs) :
  R.v23951 (state s) (inputs i) = Zmod.unsigned (N.v23951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23951 s i)) at 1.
  unfold R.v23951, N.v23951.
  unfold R.v6, N.v6.
  rewrite !state_r822_nr_5F822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r822_nr_5F822 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23952 (s : N.State) (i : N.Inputs) :
  R.v23952 (state s) (inputs i) = Zmod.unsigned (N.v23952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23952 s i)) at 1.
  unfold R.v23952, N.v23952.
  rewrite ?node_23950.
  rewrite ?node_23951.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23953 (s : N.State) (i : N.Inputs) :
  R.v23953 (state s) (inputs i) = Zmod.unsigned (N.v23953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23953 s i)) at 1.
  unfold R.v23953, N.v23953.
  unfold R.v16484, N.v16484.
  rewrite ?node_23952.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23954 (s : N.State) (i : N.Inputs) :
  R.v23954 (state s) (inputs i) = Zmod.unsigned (N.v23954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23954 s i)) at 1.
  unfold R.v23954, N.v23954.
  rewrite ?node_23947.
  rewrite ?node_23948.
  rewrite ?node_23949.
  rewrite ?node_23953.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23955 (s : N.State) (i : N.Inputs) :
  R.v23955 (state s) (inputs i) = Zmod.unsigned (N.v23955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23955 s i)) at 1.
  unfold R.v23955, N.v23955.
  unfold R.v6, N.v6.
  rewrite ?node_23954.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23956 (s : N.State) (i : N.Inputs) :
  R.v23956 (state s) (inputs i) = Zmod.unsigned (N.v23956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23956 s i)) at 1.
  unfold R.v23956, N.v23956.
  rewrite ?node_8844.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23957 (s : N.State) (i : N.Inputs) :
  R.v23957 (state s) (inputs i) = Zmod.unsigned (N.v23957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23957 s i)) at 1.
  unfold R.v23957, N.v23957.
  unfold R.v6, N.v6.
  rewrite ?node_8980.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23958 (s : N.State) (i : N.Inputs) :
  R.v23958 (state s) (inputs i) = Zmod.unsigned (N.v23958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23958 s i)) at 1.
  unfold R.v23958, N.v23958.
  unfold R.v6, N.v6.
  rewrite ?node_9029.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23959 (s : N.State) (i : N.Inputs) :
  R.v23959 (state s) (inputs i) = Zmod.unsigned (N.v23959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23959 s i)) at 1.
  unfold R.v23959, N.v23959.
  rewrite ?node_23956.
  rewrite ?node_23957.
  rewrite ?node_23958.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23960 (s : N.State) (i : N.Inputs) :
  R.v23960 (state s) (inputs i) = Zmod.unsigned (N.v23960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23960 s i)) at 1.
  unfold R.v23960, N.v23960.
  rewrite ?node_23955.
  rewrite ?node_23959.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23961 (s : N.State) (i : N.Inputs) :
  R.v23961 (state s) (inputs i) = Zmod.unsigned (N.v23961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23961 s i)) at 1.
  unfold R.v23961, N.v23961.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23962 (s : N.State) (i : N.Inputs) :
  R.v23962 (state s) (inputs i) = Zmod.unsigned (N.v23962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23962 s i)) at 1.
  unfold R.v23962, N.v23962.
  unfold R.v16463, N.v16463.
  rewrite !state_r824_nr_5F824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r824_nr_5F824 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23963 (s : N.State) (i : N.Inputs) :
  R.v23963 (state s) (inputs i) = Zmod.unsigned (N.v23963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23963 s i)) at 1.
  unfold R.v23963, N.v23963.
  unfold R.v6, N.v6.
  rewrite !state_r823_nr_5F823.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r823_nr_5F823 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23964 (s : N.State) (i : N.Inputs) :
  R.v23964 (state s) (inputs i) = Zmod.unsigned (N.v23964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23964 s i)) at 1.
  unfold R.v23964, N.v23964.
  unfold R.v6, N.v6.
  rewrite !state_r822_nr_5F822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r822_nr_5F822 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23965 (s : N.State) (i : N.Inputs) :
  R.v23965 (state s) (inputs i) = Zmod.unsigned (N.v23965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23965 s i)) at 1.
  unfold R.v23965, N.v23965.
  rewrite ?node_23963.
  rewrite ?node_23964.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23966 (s : N.State) (i : N.Inputs) :
  R.v23966 (state s) (inputs i) = Zmod.unsigned (N.v23966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23966 s i)) at 1.
  unfold R.v23966, N.v23966.
  unfold R.v16484, N.v16484.
  rewrite ?node_23965.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23967 (s : N.State) (i : N.Inputs) :
  R.v23967 (state s) (inputs i) = Zmod.unsigned (N.v23967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23967 s i)) at 1.
  unfold R.v23967, N.v23967.
  rewrite ?node_23962.
  rewrite ?node_23966.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23968 (s : N.State) (i : N.Inputs) :
  R.v23968 (state s) (inputs i) = Zmod.unsigned (N.v23968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23968 s i)) at 1.
  unfold R.v23968, N.v23968.
  unfold R.v6, N.v6.
  rewrite ?node_23967.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23969 (s : N.State) (i : N.Inputs) :
  R.v23969 (state s) (inputs i) = Zmod.unsigned (N.v23969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23969 s i)) at 1.
  unfold R.v23969, N.v23969.
  rewrite ?node_8839.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23970 (s : N.State) (i : N.Inputs) :
  R.v23970 (state s) (inputs i) = Zmod.unsigned (N.v23970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23970 s i)) at 1.
  unfold R.v23970, N.v23970.
  unfold R.v6, N.v6.
  rewrite ?node_8980.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23971 (s : N.State) (i : N.Inputs) :
  R.v23971 (state s) (inputs i) = Zmod.unsigned (N.v23971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23971 s i)) at 1.
  unfold R.v23971, N.v23971.
  rewrite ?node_23969.
  rewrite ?node_23970.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23972 (s : N.State) (i : N.Inputs) :
  R.v23972 (state s) (inputs i) = Zmod.unsigned (N.v23972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23972 s i)) at 1.
  unfold R.v23972, N.v23972.
  rewrite ?node_23968.
  rewrite ?node_23971.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23973 (s : N.State) (i : N.Inputs) :
  R.v23973 (state s) (inputs i) = Zmod.unsigned (N.v23973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23973 s i)) at 1.
  unfold R.v23973, N.v23973.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23974 (s : N.State) (i : N.Inputs) :
  R.v23974 (state s) (inputs i) = Zmod.unsigned (N.v23974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23974 s i)) at 1.
  unfold R.v23974, N.v23974.
  rewrite ?node_8843.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23975 (s : N.State) (i : N.Inputs) :
  R.v23975 (state s) (inputs i) = Zmod.unsigned (N.v23975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23975 s i)) at 1.
  unfold R.v23975, N.v23975.
  unfold R.v6, N.v6.
  rewrite !state_r825_nr_5F825.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r825_nr_5F825 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23976 (s : N.State) (i : N.Inputs) :
  R.v23976 (state s) (inputs i) = Zmod.unsigned (N.v23976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23976 s i)) at 1.
  unfold R.v23976, N.v23976.
  unfold R.v6, N.v6.
  rewrite ?node_8839.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23977 (s : N.State) (i : N.Inputs) :
  R.v23977 (state s) (inputs i) = Zmod.unsigned (N.v23977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23977 s i)) at 1.
  unfold R.v23977, N.v23977.
  rewrite ?node_23975.
  rewrite ?node_23976.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23978 (s : N.State) (i : N.Inputs) :
  R.v23978 (state s) (inputs i) = Zmod.unsigned (N.v23978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23978 s i)) at 1.
  unfold R.v23978, N.v23978.
  unfold R.v16484, N.v16484.
  rewrite ?node_23977.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23979 (s : N.State) (i : N.Inputs) :
  R.v23979 (state s) (inputs i) = Zmod.unsigned (N.v23979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23979 s i)) at 1.
  unfold R.v23979, N.v23979.
  rewrite ?node_23974.
  rewrite ?node_23978.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23980 (s : N.State) (i : N.Inputs) :
  R.v23980 (state s) (inputs i) = Zmod.unsigned (N.v23980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23980 s i)) at 1.
  unfold R.v23980, N.v23980.
  unfold R.v6, N.v6.
  rewrite ?node_23979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23981 (s : N.State) (i : N.Inputs) :
  R.v23981 (state s) (inputs i) = Zmod.unsigned (N.v23981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23981 s i)) at 1.
  unfold R.v23981, N.v23981.
  rewrite ?node_8844.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23982 (s : N.State) (i : N.Inputs) :
  R.v23982 (state s) (inputs i) = Zmod.unsigned (N.v23982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23982 s i)) at 1.
  unfold R.v23982, N.v23982.
  unfold R.v6, N.v6.
  rewrite ?node_9029.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23983 (s : N.State) (i : N.Inputs) :
  R.v23983 (state s) (inputs i) = Zmod.unsigned (N.v23983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23983 s i)) at 1.
  unfold R.v23983, N.v23983.
  rewrite ?node_23981.
  rewrite ?node_23982.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23984 (s : N.State) (i : N.Inputs) :
  R.v23984 (state s) (inputs i) = Zmod.unsigned (N.v23984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23984 s i)) at 1.
  unfold R.v23984, N.v23984.
  rewrite ?node_23980.
  rewrite ?node_23983.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23985 (s : N.State) (i : N.Inputs) :
  R.v23985 (state s) (inputs i) = Zmod.unsigned (N.v23985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23985 s i)) at 1.
  unfold R.v23985, N.v23985.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23986 (s : N.State) (i : N.Inputs) :
  R.v23986 (state s) (inputs i) = Zmod.unsigned (N.v23986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23986 s i)) at 1.
  unfold R.v23986, N.v23986.
  rewrite ?node_8855.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23987 (s : N.State) (i : N.Inputs) :
  R.v23987 (state s) (inputs i) = Zmod.unsigned (N.v23987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23987 s i)) at 1.
  unfold R.v23987, N.v23987.
  unfold R.v16463, N.v16463.
  rewrite !state_r829_nr_5F829.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r829_nr_5F829 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23988 (s : N.State) (i : N.Inputs) :
  R.v23988 (state s) (inputs i) = Zmod.unsigned (N.v23988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23988 s i)) at 1.
  unfold R.v23988, N.v23988.
  unfold R.v16463, N.v16463.
  rewrite !state_r828_nr_5F828.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r828_nr_5F828 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23989 (s : N.State) (i : N.Inputs) :
  R.v23989 (state s) (inputs i) = Zmod.unsigned (N.v23989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23989 s i)) at 1.
  unfold R.v23989, N.v23989.
  unfold R.v6, N.v6.
  rewrite !state_r827_nr_5F827.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r827_nr_5F827 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23990 (s : N.State) (i : N.Inputs) :
  R.v23990 (state s) (inputs i) = Zmod.unsigned (N.v23990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23990 s i)) at 1.
  unfold R.v23990, N.v23990.
  unfold R.v6, N.v6.
  rewrite !state_r826_nr_5F826.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r826_nr_5F826 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23991 (s : N.State) (i : N.Inputs) :
  R.v23991 (state s) (inputs i) = Zmod.unsigned (N.v23991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23991 s i)) at 1.
  unfold R.v23991, N.v23991.
  rewrite ?node_23989.
  rewrite ?node_23990.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23992 (s : N.State) (i : N.Inputs) :
  R.v23992 (state s) (inputs i) = Zmod.unsigned (N.v23992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23992 s i)) at 1.
  unfold R.v23992, N.v23992.
  unfold R.v16484, N.v16484.
  rewrite ?node_23991.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23993 (s : N.State) (i : N.Inputs) :
  R.v23993 (state s) (inputs i) = Zmod.unsigned (N.v23993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23993 s i)) at 1.
  unfold R.v23993, N.v23993.
  rewrite ?node_23986.
  rewrite ?node_23987.
  rewrite ?node_23988.
  rewrite ?node_23992.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23994 (s : N.State) (i : N.Inputs) :
  R.v23994 (state s) (inputs i) = Zmod.unsigned (N.v23994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23994 s i)) at 1.
  unfold R.v23994, N.v23994.
  unfold R.v6, N.v6.
  rewrite ?node_23993.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23995 (s : N.State) (i : N.Inputs) :
  R.v23995 (state s) (inputs i) = Zmod.unsigned (N.v23995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23995 s i)) at 1.
  unfold R.v23995, N.v23995.
  rewrite ?node_8856.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23996 (s : N.State) (i : N.Inputs) :
  R.v23996 (state s) (inputs i) = Zmod.unsigned (N.v23996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23996 s i)) at 1.
  unfold R.v23996, N.v23996.
  unfold R.v6, N.v6.
  rewrite ?node_8992.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23997 (s : N.State) (i : N.Inputs) :
  R.v23997 (state s) (inputs i) = Zmod.unsigned (N.v23997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23997 s i)) at 1.
  unfold R.v23997, N.v23997.
  unfold R.v6, N.v6.
  rewrite ?node_9038.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23998 (s : N.State) (i : N.Inputs) :
  R.v23998 (state s) (inputs i) = Zmod.unsigned (N.v23998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23998 s i)) at 1.
  unfold R.v23998, N.v23998.
  rewrite ?node_23995.
  rewrite ?node_23996.
  rewrite ?node_23997.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_23999 (s : N.State) (i : N.Inputs) :
  R.v23999 (state s) (inputs i) = Zmod.unsigned (N.v23999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v23999 s i)) at 1.
  unfold R.v23999, N.v23999.
  rewrite ?node_23994.
  rewrite ?node_23998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
