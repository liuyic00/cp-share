(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes023.
Lemma node_24000 (s : N.State) (i : N.Inputs) :
  R.v24000 (state s) (inputs i) = Zmod.unsigned (N.v24000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24000 s i)) at 1.
  unfold R.v24000, N.v24000.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24001 (s : N.State) (i : N.Inputs) :
  R.v24001 (state s) (inputs i) = Zmod.unsigned (N.v24001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24001 s i)) at 1.
  unfold R.v24001, N.v24001.
  unfold R.v16463, N.v16463.
  rewrite !state_r828_nr_5F828.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r828_nr_5F828 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24002 (s : N.State) (i : N.Inputs) :
  R.v24002 (state s) (inputs i) = Zmod.unsigned (N.v24002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24002 s i)) at 1.
  unfold R.v24002, N.v24002.
  unfold R.v6, N.v6.
  rewrite !state_r827_nr_5F827.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r827_nr_5F827 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24003 (s : N.State) (i : N.Inputs) :
  R.v24003 (state s) (inputs i) = Zmod.unsigned (N.v24003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24003 s i)) at 1.
  unfold R.v24003, N.v24003.
  unfold R.v6, N.v6.
  rewrite !state_r826_nr_5F826.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r826_nr_5F826 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24004 (s : N.State) (i : N.Inputs) :
  R.v24004 (state s) (inputs i) = Zmod.unsigned (N.v24004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24004 s i)) at 1.
  unfold R.v24004, N.v24004.
  rewrite ?node_24002.
  rewrite ?node_24003.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24005 (s : N.State) (i : N.Inputs) :
  R.v24005 (state s) (inputs i) = Zmod.unsigned (N.v24005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24005 s i)) at 1.
  unfold R.v24005, N.v24005.
  unfold R.v16484, N.v16484.
  rewrite ?node_24004.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24006 (s : N.State) (i : N.Inputs) :
  R.v24006 (state s) (inputs i) = Zmod.unsigned (N.v24006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24006 s i)) at 1.
  unfold R.v24006, N.v24006.
  rewrite ?node_24001.
  rewrite ?node_24005.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24007 (s : N.State) (i : N.Inputs) :
  R.v24007 (state s) (inputs i) = Zmod.unsigned (N.v24007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24007 s i)) at 1.
  unfold R.v24007, N.v24007.
  unfold R.v6, N.v6.
  rewrite ?node_24006.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24008 (s : N.State) (i : N.Inputs) :
  R.v24008 (state s) (inputs i) = Zmod.unsigned (N.v24008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24008 s i)) at 1.
  unfold R.v24008, N.v24008.
  rewrite ?node_8851.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24009 (s : N.State) (i : N.Inputs) :
  R.v24009 (state s) (inputs i) = Zmod.unsigned (N.v24009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24009 s i)) at 1.
  unfold R.v24009, N.v24009.
  unfold R.v6, N.v6.
  rewrite ?node_8992.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24010 (s : N.State) (i : N.Inputs) :
  R.v24010 (state s) (inputs i) = Zmod.unsigned (N.v24010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24010 s i)) at 1.
  unfold R.v24010, N.v24010.
  rewrite ?node_24008.
  rewrite ?node_24009.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24011 (s : N.State) (i : N.Inputs) :
  R.v24011 (state s) (inputs i) = Zmod.unsigned (N.v24011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24011 s i)) at 1.
  unfold R.v24011, N.v24011.
  rewrite ?node_24007.
  rewrite ?node_24010.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24012 (s : N.State) (i : N.Inputs) :
  R.v24012 (state s) (inputs i) = Zmod.unsigned (N.v24012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24012 s i)) at 1.
  unfold R.v24012, N.v24012.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24013 (s : N.State) (i : N.Inputs) :
  R.v24013 (state s) (inputs i) = Zmod.unsigned (N.v24013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24013 s i)) at 1.
  unfold R.v24013, N.v24013.
  rewrite ?node_8855.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24014 (s : N.State) (i : N.Inputs) :
  R.v24014 (state s) (inputs i) = Zmod.unsigned (N.v24014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24014 s i)) at 1.
  unfold R.v24014, N.v24014.
  unfold R.v6, N.v6.
  rewrite !state_r829_nr_5F829.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r829_nr_5F829 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24015 (s : N.State) (i : N.Inputs) :
  R.v24015 (state s) (inputs i) = Zmod.unsigned (N.v24015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24015 s i)) at 1.
  unfold R.v24015, N.v24015.
  unfold R.v6, N.v6.
  rewrite ?node_8851.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24016 (s : N.State) (i : N.Inputs) :
  R.v24016 (state s) (inputs i) = Zmod.unsigned (N.v24016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24016 s i)) at 1.
  unfold R.v24016, N.v24016.
  rewrite ?node_24014.
  rewrite ?node_24015.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24017 (s : N.State) (i : N.Inputs) :
  R.v24017 (state s) (inputs i) = Zmod.unsigned (N.v24017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24017 s i)) at 1.
  unfold R.v24017, N.v24017.
  unfold R.v16484, N.v16484.
  rewrite ?node_24016.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24018 (s : N.State) (i : N.Inputs) :
  R.v24018 (state s) (inputs i) = Zmod.unsigned (N.v24018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24018 s i)) at 1.
  unfold R.v24018, N.v24018.
  rewrite ?node_24013.
  rewrite ?node_24017.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24019 (s : N.State) (i : N.Inputs) :
  R.v24019 (state s) (inputs i) = Zmod.unsigned (N.v24019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24019 s i)) at 1.
  unfold R.v24019, N.v24019.
  unfold R.v6, N.v6.
  rewrite ?node_24018.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24020 (s : N.State) (i : N.Inputs) :
  R.v24020 (state s) (inputs i) = Zmod.unsigned (N.v24020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24020 s i)) at 1.
  unfold R.v24020, N.v24020.
  rewrite ?node_8856.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24021 (s : N.State) (i : N.Inputs) :
  R.v24021 (state s) (inputs i) = Zmod.unsigned (N.v24021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24021 s i)) at 1.
  unfold R.v24021, N.v24021.
  unfold R.v6, N.v6.
  rewrite ?node_9038.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24022 (s : N.State) (i : N.Inputs) :
  R.v24022 (state s) (inputs i) = Zmod.unsigned (N.v24022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24022 s i)) at 1.
  unfold R.v24022, N.v24022.
  rewrite ?node_24020.
  rewrite ?node_24021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24023 (s : N.State) (i : N.Inputs) :
  R.v24023 (state s) (inputs i) = Zmod.unsigned (N.v24023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24023 s i)) at 1.
  unfold R.v24023, N.v24023.
  rewrite ?node_24019.
  rewrite ?node_24022.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24024 (s : N.State) (i : N.Inputs) :
  R.v24024 (state s) (inputs i) = Zmod.unsigned (N.v24024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24024 s i)) at 1.
  unfold R.v24024, N.v24024.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24025 (s : N.State) (i : N.Inputs) :
  R.v24025 (state s) (inputs i) = Zmod.unsigned (N.v24025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24025 s i)) at 1.
  unfold R.v24025, N.v24025.
  rewrite ?node_8862.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24026 (s : N.State) (i : N.Inputs) :
  R.v24026 (state s) (inputs i) = Zmod.unsigned (N.v24026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24026 s i)) at 1.
  unfold R.v24026, N.v24026.
  unfold R.v16463, N.v16463.
  rewrite !state_r833_nr_5F833.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r833_nr_5F833 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24027 (s : N.State) (i : N.Inputs) :
  R.v24027 (state s) (inputs i) = Zmod.unsigned (N.v24027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24027 s i)) at 1.
  unfold R.v24027, N.v24027.
  unfold R.v16463, N.v16463.
  rewrite !state_r832_nr_5F832.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r832_nr_5F832 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24028 (s : N.State) (i : N.Inputs) :
  R.v24028 (state s) (inputs i) = Zmod.unsigned (N.v24028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24028 s i)) at 1.
  unfold R.v24028, N.v24028.
  unfold R.v6, N.v6.
  rewrite !state_r831_nr_5F831.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r831_nr_5F831 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24029 (s : N.State) (i : N.Inputs) :
  R.v24029 (state s) (inputs i) = Zmod.unsigned (N.v24029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24029 s i)) at 1.
  unfold R.v24029, N.v24029.
  unfold R.v6, N.v6.
  rewrite !state_r830_nr_5F830.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r830_nr_5F830 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24030 (s : N.State) (i : N.Inputs) :
  R.v24030 (state s) (inputs i) = Zmod.unsigned (N.v24030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24030 s i)) at 1.
  unfold R.v24030, N.v24030.
  rewrite ?node_24028.
  rewrite ?node_24029.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24031 (s : N.State) (i : N.Inputs) :
  R.v24031 (state s) (inputs i) = Zmod.unsigned (N.v24031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24031 s i)) at 1.
  unfold R.v24031, N.v24031.
  unfold R.v16484, N.v16484.
  rewrite ?node_24030.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24032 (s : N.State) (i : N.Inputs) :
  R.v24032 (state s) (inputs i) = Zmod.unsigned (N.v24032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24032 s i)) at 1.
  unfold R.v24032, N.v24032.
  rewrite ?node_24025.
  rewrite ?node_24026.
  rewrite ?node_24027.
  rewrite ?node_24031.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24033 (s : N.State) (i : N.Inputs) :
  R.v24033 (state s) (inputs i) = Zmod.unsigned (N.v24033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24033 s i)) at 1.
  unfold R.v24033, N.v24033.
  unfold R.v6, N.v6.
  rewrite ?node_24032.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24034 (s : N.State) (i : N.Inputs) :
  R.v24034 (state s) (inputs i) = Zmod.unsigned (N.v24034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24034 s i)) at 1.
  unfold R.v24034, N.v24034.
  rewrite ?node_8863.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24035 (s : N.State) (i : N.Inputs) :
  R.v24035 (state s) (inputs i) = Zmod.unsigned (N.v24035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24035 s i)) at 1.
  unfold R.v24035, N.v24035.
  unfold R.v6, N.v6.
  rewrite ?node_8999.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24036 (s : N.State) (i : N.Inputs) :
  R.v24036 (state s) (inputs i) = Zmod.unsigned (N.v24036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24036 s i)) at 1.
  unfold R.v24036, N.v24036.
  unfold R.v6, N.v6.
  rewrite ?node_9041.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24037 (s : N.State) (i : N.Inputs) :
  R.v24037 (state s) (inputs i) = Zmod.unsigned (N.v24037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24037 s i)) at 1.
  unfold R.v24037, N.v24037.
  rewrite ?node_24034.
  rewrite ?node_24035.
  rewrite ?node_24036.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24038 (s : N.State) (i : N.Inputs) :
  R.v24038 (state s) (inputs i) = Zmod.unsigned (N.v24038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24038 s i)) at 1.
  unfold R.v24038, N.v24038.
  rewrite ?node_24033.
  rewrite ?node_24037.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24039 (s : N.State) (i : N.Inputs) :
  R.v24039 (state s) (inputs i) = Zmod.unsigned (N.v24039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24039 s i)) at 1.
  unfold R.v24039, N.v24039.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24040 (s : N.State) (i : N.Inputs) :
  R.v24040 (state s) (inputs i) = Zmod.unsigned (N.v24040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24040 s i)) at 1.
  unfold R.v24040, N.v24040.
  unfold R.v16463, N.v16463.
  rewrite !state_r832_nr_5F832.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r832_nr_5F832 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24041 (s : N.State) (i : N.Inputs) :
  R.v24041 (state s) (inputs i) = Zmod.unsigned (N.v24041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24041 s i)) at 1.
  unfold R.v24041, N.v24041.
  unfold R.v6, N.v6.
  rewrite !state_r831_nr_5F831.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r831_nr_5F831 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24042 (s : N.State) (i : N.Inputs) :
  R.v24042 (state s) (inputs i) = Zmod.unsigned (N.v24042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24042 s i)) at 1.
  unfold R.v24042, N.v24042.
  unfold R.v6, N.v6.
  rewrite !state_r830_nr_5F830.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r830_nr_5F830 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24043 (s : N.State) (i : N.Inputs) :
  R.v24043 (state s) (inputs i) = Zmod.unsigned (N.v24043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24043 s i)) at 1.
  unfold R.v24043, N.v24043.
  rewrite ?node_24041.
  rewrite ?node_24042.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24044 (s : N.State) (i : N.Inputs) :
  R.v24044 (state s) (inputs i) = Zmod.unsigned (N.v24044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24044 s i)) at 1.
  unfold R.v24044, N.v24044.
  unfold R.v16484, N.v16484.
  rewrite ?node_24043.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24045 (s : N.State) (i : N.Inputs) :
  R.v24045 (state s) (inputs i) = Zmod.unsigned (N.v24045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24045 s i)) at 1.
  unfold R.v24045, N.v24045.
  rewrite ?node_24040.
  rewrite ?node_24044.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24046 (s : N.State) (i : N.Inputs) :
  R.v24046 (state s) (inputs i) = Zmod.unsigned (N.v24046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24046 s i)) at 1.
  unfold R.v24046, N.v24046.
  unfold R.v6, N.v6.
  rewrite ?node_24045.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24047 (s : N.State) (i : N.Inputs) :
  R.v24047 (state s) (inputs i) = Zmod.unsigned (N.v24047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24047 s i)) at 1.
  unfold R.v24047, N.v24047.
  rewrite ?node_8858.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24048 (s : N.State) (i : N.Inputs) :
  R.v24048 (state s) (inputs i) = Zmod.unsigned (N.v24048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24048 s i)) at 1.
  unfold R.v24048, N.v24048.
  unfold R.v6, N.v6.
  rewrite ?node_8999.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24049 (s : N.State) (i : N.Inputs) :
  R.v24049 (state s) (inputs i) = Zmod.unsigned (N.v24049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24049 s i)) at 1.
  unfold R.v24049, N.v24049.
  rewrite ?node_24047.
  rewrite ?node_24048.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24050 (s : N.State) (i : N.Inputs) :
  R.v24050 (state s) (inputs i) = Zmod.unsigned (N.v24050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24050 s i)) at 1.
  unfold R.v24050, N.v24050.
  rewrite ?node_24046.
  rewrite ?node_24049.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24051 (s : N.State) (i : N.Inputs) :
  R.v24051 (state s) (inputs i) = Zmod.unsigned (N.v24051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24051 s i)) at 1.
  unfold R.v24051, N.v24051.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24052 (s : N.State) (i : N.Inputs) :
  R.v24052 (state s) (inputs i) = Zmod.unsigned (N.v24052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24052 s i)) at 1.
  unfold R.v24052, N.v24052.
  rewrite ?node_8862.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24053 (s : N.State) (i : N.Inputs) :
  R.v24053 (state s) (inputs i) = Zmod.unsigned (N.v24053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24053 s i)) at 1.
  unfold R.v24053, N.v24053.
  unfold R.v6, N.v6.
  rewrite !state_r833_nr_5F833.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r833_nr_5F833 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24054 (s : N.State) (i : N.Inputs) :
  R.v24054 (state s) (inputs i) = Zmod.unsigned (N.v24054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24054 s i)) at 1.
  unfold R.v24054, N.v24054.
  unfold R.v6, N.v6.
  rewrite ?node_8858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24055 (s : N.State) (i : N.Inputs) :
  R.v24055 (state s) (inputs i) = Zmod.unsigned (N.v24055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24055 s i)) at 1.
  unfold R.v24055, N.v24055.
  rewrite ?node_24053.
  rewrite ?node_24054.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24056 (s : N.State) (i : N.Inputs) :
  R.v24056 (state s) (inputs i) = Zmod.unsigned (N.v24056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24056 s i)) at 1.
  unfold R.v24056, N.v24056.
  unfold R.v16484, N.v16484.
  rewrite ?node_24055.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24057 (s : N.State) (i : N.Inputs) :
  R.v24057 (state s) (inputs i) = Zmod.unsigned (N.v24057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24057 s i)) at 1.
  unfold R.v24057, N.v24057.
  rewrite ?node_24052.
  rewrite ?node_24056.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24058 (s : N.State) (i : N.Inputs) :
  R.v24058 (state s) (inputs i) = Zmod.unsigned (N.v24058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24058 s i)) at 1.
  unfold R.v24058, N.v24058.
  unfold R.v6, N.v6.
  rewrite ?node_24057.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24059 (s : N.State) (i : N.Inputs) :
  R.v24059 (state s) (inputs i) = Zmod.unsigned (N.v24059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24059 s i)) at 1.
  unfold R.v24059, N.v24059.
  rewrite ?node_8863.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24060 (s : N.State) (i : N.Inputs) :
  R.v24060 (state s) (inputs i) = Zmod.unsigned (N.v24060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24060 s i)) at 1.
  unfold R.v24060, N.v24060.
  unfold R.v6, N.v6.
  rewrite ?node_9041.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24061 (s : N.State) (i : N.Inputs) :
  R.v24061 (state s) (inputs i) = Zmod.unsigned (N.v24061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24061 s i)) at 1.
  unfold R.v24061, N.v24061.
  rewrite ?node_24059.
  rewrite ?node_24060.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24062 (s : N.State) (i : N.Inputs) :
  R.v24062 (state s) (inputs i) = Zmod.unsigned (N.v24062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24062 s i)) at 1.
  unfold R.v24062, N.v24062.
  rewrite ?node_24058.
  rewrite ?node_24061.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24063 (s : N.State) (i : N.Inputs) :
  R.v24063 (state s) (inputs i) = Zmod.unsigned (N.v24063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24063 s i)) at 1.
  unfold R.v24063, N.v24063.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24064 (s : N.State) (i : N.Inputs) :
  R.v24064 (state s) (inputs i) = Zmod.unsigned (N.v24064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24064 s i)) at 1.
  unfold R.v24064, N.v24064.
  rewrite ?node_8870.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24065 (s : N.State) (i : N.Inputs) :
  R.v24065 (state s) (inputs i) = Zmod.unsigned (N.v24065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24065 s i)) at 1.
  unfold R.v24065, N.v24065.
  unfold R.v16463, N.v16463.
  rewrite !state_r837_nr_5F837.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r837_nr_5F837 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24066 (s : N.State) (i : N.Inputs) :
  R.v24066 (state s) (inputs i) = Zmod.unsigned (N.v24066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24066 s i)) at 1.
  unfold R.v24066, N.v24066.
  unfold R.v16463, N.v16463.
  rewrite !state_r836_nr_5F836.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r836_nr_5F836 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24067 (s : N.State) (i : N.Inputs) :
  R.v24067 (state s) (inputs i) = Zmod.unsigned (N.v24067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24067 s i)) at 1.
  unfold R.v24067, N.v24067.
  unfold R.v6, N.v6.
  rewrite !state_r835_nr_5F835.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r835_nr_5F835 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24068 (s : N.State) (i : N.Inputs) :
  R.v24068 (state s) (inputs i) = Zmod.unsigned (N.v24068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24068 s i)) at 1.
  unfold R.v24068, N.v24068.
  unfold R.v6, N.v6.
  rewrite !state_r834_nr_5F834.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r834_nr_5F834 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24069 (s : N.State) (i : N.Inputs) :
  R.v24069 (state s) (inputs i) = Zmod.unsigned (N.v24069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24069 s i)) at 1.
  unfold R.v24069, N.v24069.
  rewrite ?node_24067.
  rewrite ?node_24068.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24070 (s : N.State) (i : N.Inputs) :
  R.v24070 (state s) (inputs i) = Zmod.unsigned (N.v24070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24070 s i)) at 1.
  unfold R.v24070, N.v24070.
  unfold R.v16484, N.v16484.
  rewrite ?node_24069.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24071 (s : N.State) (i : N.Inputs) :
  R.v24071 (state s) (inputs i) = Zmod.unsigned (N.v24071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24071 s i)) at 1.
  unfold R.v24071, N.v24071.
  rewrite ?node_24064.
  rewrite ?node_24065.
  rewrite ?node_24066.
  rewrite ?node_24070.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24072 (s : N.State) (i : N.Inputs) :
  R.v24072 (state s) (inputs i) = Zmod.unsigned (N.v24072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24072 s i)) at 1.
  unfold R.v24072, N.v24072.
  unfold R.v6, N.v6.
  rewrite ?node_24071.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24073 (s : N.State) (i : N.Inputs) :
  R.v24073 (state s) (inputs i) = Zmod.unsigned (N.v24073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24073 s i)) at 1.
  unfold R.v24073, N.v24073.
  rewrite ?node_8871.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24074 (s : N.State) (i : N.Inputs) :
  R.v24074 (state s) (inputs i) = Zmod.unsigned (N.v24074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24074 s i)) at 1.
  unfold R.v24074, N.v24074.
  unfold R.v6, N.v6.
  rewrite ?node_9007.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24075 (s : N.State) (i : N.Inputs) :
  R.v24075 (state s) (inputs i) = Zmod.unsigned (N.v24075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24075 s i)) at 1.
  unfold R.v24075, N.v24075.
  unfold R.v6, N.v6.
  rewrite ?node_9045.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24076 (s : N.State) (i : N.Inputs) :
  R.v24076 (state s) (inputs i) = Zmod.unsigned (N.v24076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24076 s i)) at 1.
  unfold R.v24076, N.v24076.
  rewrite ?node_24073.
  rewrite ?node_24074.
  rewrite ?node_24075.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24077 (s : N.State) (i : N.Inputs) :
  R.v24077 (state s) (inputs i) = Zmod.unsigned (N.v24077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24077 s i)) at 1.
  unfold R.v24077, N.v24077.
  rewrite ?node_24072.
  rewrite ?node_24076.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24078 (s : N.State) (i : N.Inputs) :
  R.v24078 (state s) (inputs i) = Zmod.unsigned (N.v24078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24078 s i)) at 1.
  unfold R.v24078, N.v24078.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24079 (s : N.State) (i : N.Inputs) :
  R.v24079 (state s) (inputs i) = Zmod.unsigned (N.v24079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24079 s i)) at 1.
  unfold R.v24079, N.v24079.
  unfold R.v16463, N.v16463.
  rewrite !state_r836_nr_5F836.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r836_nr_5F836 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24080 (s : N.State) (i : N.Inputs) :
  R.v24080 (state s) (inputs i) = Zmod.unsigned (N.v24080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24080 s i)) at 1.
  unfold R.v24080, N.v24080.
  unfold R.v6, N.v6.
  rewrite !state_r835_nr_5F835.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r835_nr_5F835 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24081 (s : N.State) (i : N.Inputs) :
  R.v24081 (state s) (inputs i) = Zmod.unsigned (N.v24081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24081 s i)) at 1.
  unfold R.v24081, N.v24081.
  unfold R.v6, N.v6.
  rewrite !state_r834_nr_5F834.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r834_nr_5F834 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24082 (s : N.State) (i : N.Inputs) :
  R.v24082 (state s) (inputs i) = Zmod.unsigned (N.v24082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24082 s i)) at 1.
  unfold R.v24082, N.v24082.
  rewrite ?node_24080.
  rewrite ?node_24081.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24083 (s : N.State) (i : N.Inputs) :
  R.v24083 (state s) (inputs i) = Zmod.unsigned (N.v24083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24083 s i)) at 1.
  unfold R.v24083, N.v24083.
  unfold R.v16484, N.v16484.
  rewrite ?node_24082.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24084 (s : N.State) (i : N.Inputs) :
  R.v24084 (state s) (inputs i) = Zmod.unsigned (N.v24084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24084 s i)) at 1.
  unfold R.v24084, N.v24084.
  rewrite ?node_24079.
  rewrite ?node_24083.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24085 (s : N.State) (i : N.Inputs) :
  R.v24085 (state s) (inputs i) = Zmod.unsigned (N.v24085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24085 s i)) at 1.
  unfold R.v24085, N.v24085.
  unfold R.v6, N.v6.
  rewrite ?node_24084.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24086 (s : N.State) (i : N.Inputs) :
  R.v24086 (state s) (inputs i) = Zmod.unsigned (N.v24086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24086 s i)) at 1.
  unfold R.v24086, N.v24086.
  rewrite ?node_8866.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24087 (s : N.State) (i : N.Inputs) :
  R.v24087 (state s) (inputs i) = Zmod.unsigned (N.v24087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24087 s i)) at 1.
  unfold R.v24087, N.v24087.
  unfold R.v6, N.v6.
  rewrite ?node_9007.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24088 (s : N.State) (i : N.Inputs) :
  R.v24088 (state s) (inputs i) = Zmod.unsigned (N.v24088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24088 s i)) at 1.
  unfold R.v24088, N.v24088.
  rewrite ?node_24086.
  rewrite ?node_24087.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24089 (s : N.State) (i : N.Inputs) :
  R.v24089 (state s) (inputs i) = Zmod.unsigned (N.v24089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24089 s i)) at 1.
  unfold R.v24089, N.v24089.
  rewrite ?node_24085.
  rewrite ?node_24088.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24090 (s : N.State) (i : N.Inputs) :
  R.v24090 (state s) (inputs i) = Zmod.unsigned (N.v24090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24090 s i)) at 1.
  unfold R.v24090, N.v24090.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24091 (s : N.State) (i : N.Inputs) :
  R.v24091 (state s) (inputs i) = Zmod.unsigned (N.v24091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24091 s i)) at 1.
  unfold R.v24091, N.v24091.
  rewrite ?node_8870.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24092 (s : N.State) (i : N.Inputs) :
  R.v24092 (state s) (inputs i) = Zmod.unsigned (N.v24092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24092 s i)) at 1.
  unfold R.v24092, N.v24092.
  unfold R.v6, N.v6.
  rewrite !state_r837_nr_5F837.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r837_nr_5F837 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24093 (s : N.State) (i : N.Inputs) :
  R.v24093 (state s) (inputs i) = Zmod.unsigned (N.v24093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24093 s i)) at 1.
  unfold R.v24093, N.v24093.
  unfold R.v6, N.v6.
  rewrite ?node_8866.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24094 (s : N.State) (i : N.Inputs) :
  R.v24094 (state s) (inputs i) = Zmod.unsigned (N.v24094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24094 s i)) at 1.
  unfold R.v24094, N.v24094.
  rewrite ?node_24092.
  rewrite ?node_24093.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24095 (s : N.State) (i : N.Inputs) :
  R.v24095 (state s) (inputs i) = Zmod.unsigned (N.v24095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24095 s i)) at 1.
  unfold R.v24095, N.v24095.
  unfold R.v16484, N.v16484.
  rewrite ?node_24094.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24096 (s : N.State) (i : N.Inputs) :
  R.v24096 (state s) (inputs i) = Zmod.unsigned (N.v24096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24096 s i)) at 1.
  unfold R.v24096, N.v24096.
  rewrite ?node_24091.
  rewrite ?node_24095.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24097 (s : N.State) (i : N.Inputs) :
  R.v24097 (state s) (inputs i) = Zmod.unsigned (N.v24097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24097 s i)) at 1.
  unfold R.v24097, N.v24097.
  unfold R.v6, N.v6.
  rewrite ?node_24096.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24098 (s : N.State) (i : N.Inputs) :
  R.v24098 (state s) (inputs i) = Zmod.unsigned (N.v24098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24098 s i)) at 1.
  unfold R.v24098, N.v24098.
  rewrite ?node_8871.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24099 (s : N.State) (i : N.Inputs) :
  R.v24099 (state s) (inputs i) = Zmod.unsigned (N.v24099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24099 s i)) at 1.
  unfold R.v24099, N.v24099.
  unfold R.v6, N.v6.
  rewrite ?node_9045.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24100 (s : N.State) (i : N.Inputs) :
  R.v24100 (state s) (inputs i) = Zmod.unsigned (N.v24100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24100 s i)) at 1.
  unfold R.v24100, N.v24100.
  rewrite ?node_24098.
  rewrite ?node_24099.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24101 (s : N.State) (i : N.Inputs) :
  R.v24101 (state s) (inputs i) = Zmod.unsigned (N.v24101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24101 s i)) at 1.
  unfold R.v24101, N.v24101.
  rewrite ?node_24097.
  rewrite ?node_24100.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24102 (s : N.State) (i : N.Inputs) :
  R.v24102 (state s) (inputs i) = Zmod.unsigned (N.v24102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24102 s i)) at 1.
  unfold R.v24102, N.v24102.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24103 (s : N.State) (i : N.Inputs) :
  R.v24103 (state s) (inputs i) = Zmod.unsigned (N.v24103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24103 s i)) at 1.
  unfold R.v24103, N.v24103.
  rewrite ?node_8957.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24104 (s : N.State) (i : N.Inputs) :
  R.v24104 (state s) (inputs i) = Zmod.unsigned (N.v24104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24104 s i)) at 1.
  unfold R.v24104, N.v24104.
  unfold R.v16463, N.v16463.
  rewrite !state_r842_nr_5F842.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r842_nr_5F842 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24105 (s : N.State) (i : N.Inputs) :
  R.v24105 (state s) (inputs i) = Zmod.unsigned (N.v24105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24105 s i)) at 1.
  unfold R.v24105, N.v24105.
  unfold R.v16463, N.v16463.
  rewrite !state_r841_nr_5F841.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r841_nr_5F841 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24106 (s : N.State) (i : N.Inputs) :
  R.v24106 (state s) (inputs i) = Zmod.unsigned (N.v24106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24106 s i)) at 1.
  unfold R.v24106, N.v24106.
  unfold R.v6, N.v6.
  rewrite !state_r840_nr_5F840.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r840_nr_5F840 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24107 (s : N.State) (i : N.Inputs) :
  R.v24107 (state s) (inputs i) = Zmod.unsigned (N.v24107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24107 s i)) at 1.
  unfold R.v24107, N.v24107.
  unfold R.v6, N.v6.
  rewrite !state_r839_nr_5F839.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r839_nr_5F839 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24108 (s : N.State) (i : N.Inputs) :
  R.v24108 (state s) (inputs i) = Zmod.unsigned (N.v24108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24108 s i)) at 1.
  unfold R.v24108, N.v24108.
  rewrite ?node_24106.
  rewrite ?node_24107.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24109 (s : N.State) (i : N.Inputs) :
  R.v24109 (state s) (inputs i) = Zmod.unsigned (N.v24109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24109 s i)) at 1.
  unfold R.v24109, N.v24109.
  unfold R.v16484, N.v16484.
  rewrite ?node_24108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24110 (s : N.State) (i : N.Inputs) :
  R.v24110 (state s) (inputs i) = Zmod.unsigned (N.v24110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24110 s i)) at 1.
  unfold R.v24110, N.v24110.
  rewrite ?node_24103.
  rewrite ?node_24104.
  rewrite ?node_24105.
  rewrite ?node_24109.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24111 (s : N.State) (i : N.Inputs) :
  R.v24111 (state s) (inputs i) = Zmod.unsigned (N.v24111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24111 s i)) at 1.
  unfold R.v24111, N.v24111.
  unfold R.v6, N.v6.
  rewrite ?node_24110.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24112 (s : N.State) (i : N.Inputs) :
  R.v24112 (state s) (inputs i) = Zmod.unsigned (N.v24112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24112 s i)) at 1.
  unfold R.v24112, N.v24112.
  rewrite ?node_8958.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24113 (s : N.State) (i : N.Inputs) :
  R.v24113 (state s) (inputs i) = Zmod.unsigned (N.v24113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24113 s i)) at 1.
  unfold R.v24113, N.v24113.
  unfold R.v6, N.v6.
  rewrite ?node_9096.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24114 (s : N.State) (i : N.Inputs) :
  R.v24114 (state s) (inputs i) = Zmod.unsigned (N.v24114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24114 s i)) at 1.
  unfold R.v24114, N.v24114.
  unfold R.v6, N.v6.
  rewrite ?node_9158.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24115 (s : N.State) (i : N.Inputs) :
  R.v24115 (state s) (inputs i) = Zmod.unsigned (N.v24115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24115 s i)) at 1.
  unfold R.v24115, N.v24115.
  rewrite ?node_24112.
  rewrite ?node_24113.
  rewrite ?node_24114.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24116 (s : N.State) (i : N.Inputs) :
  R.v24116 (state s) (inputs i) = Zmod.unsigned (N.v24116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24116 s i)) at 1.
  unfold R.v24116, N.v24116.
  rewrite ?node_24111.
  rewrite ?node_24115.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24117 (s : N.State) (i : N.Inputs) :
  R.v24117 (state s) (inputs i) = Zmod.unsigned (N.v24117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24117 s i)) at 1.
  unfold R.v24117, N.v24117.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24118 (s : N.State) (i : N.Inputs) :
  R.v24118 (state s) (inputs i) = Zmod.unsigned (N.v24118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24118 s i)) at 1.
  unfold R.v24118, N.v24118.
  unfold R.v16463, N.v16463.
  rewrite !state_r841_nr_5F841.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r841_nr_5F841 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24119 (s : N.State) (i : N.Inputs) :
  R.v24119 (state s) (inputs i) = Zmod.unsigned (N.v24119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24119 s i)) at 1.
  unfold R.v24119, N.v24119.
  unfold R.v6, N.v6.
  rewrite !state_r840_nr_5F840.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r840_nr_5F840 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24120 (s : N.State) (i : N.Inputs) :
  R.v24120 (state s) (inputs i) = Zmod.unsigned (N.v24120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24120 s i)) at 1.
  unfold R.v24120, N.v24120.
  unfold R.v6, N.v6.
  rewrite !state_r839_nr_5F839.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r839_nr_5F839 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24121 (s : N.State) (i : N.Inputs) :
  R.v24121 (state s) (inputs i) = Zmod.unsigned (N.v24121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24121 s i)) at 1.
  unfold R.v24121, N.v24121.
  rewrite ?node_24119.
  rewrite ?node_24120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24122 (s : N.State) (i : N.Inputs) :
  R.v24122 (state s) (inputs i) = Zmod.unsigned (N.v24122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24122 s i)) at 1.
  unfold R.v24122, N.v24122.
  unfold R.v16484, N.v16484.
  rewrite ?node_24121.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24123 (s : N.State) (i : N.Inputs) :
  R.v24123 (state s) (inputs i) = Zmod.unsigned (N.v24123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24123 s i)) at 1.
  unfold R.v24123, N.v24123.
  rewrite ?node_24118.
  rewrite ?node_24122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24124 (s : N.State) (i : N.Inputs) :
  R.v24124 (state s) (inputs i) = Zmod.unsigned (N.v24124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24124 s i)) at 1.
  unfold R.v24124, N.v24124.
  unfold R.v6, N.v6.
  rewrite ?node_24123.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24125 (s : N.State) (i : N.Inputs) :
  R.v24125 (state s) (inputs i) = Zmod.unsigned (N.v24125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24125 s i)) at 1.
  unfold R.v24125, N.v24125.
  rewrite ?node_8953.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24126 (s : N.State) (i : N.Inputs) :
  R.v24126 (state s) (inputs i) = Zmod.unsigned (N.v24126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24126 s i)) at 1.
  unfold R.v24126, N.v24126.
  unfold R.v6, N.v6.
  rewrite ?node_9096.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24127 (s : N.State) (i : N.Inputs) :
  R.v24127 (state s) (inputs i) = Zmod.unsigned (N.v24127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24127 s i)) at 1.
  unfold R.v24127, N.v24127.
  rewrite ?node_24125.
  rewrite ?node_24126.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24128 (s : N.State) (i : N.Inputs) :
  R.v24128 (state s) (inputs i) = Zmod.unsigned (N.v24128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24128 s i)) at 1.
  unfold R.v24128, N.v24128.
  rewrite ?node_24124.
  rewrite ?node_24127.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24129 (s : N.State) (i : N.Inputs) :
  R.v24129 (state s) (inputs i) = Zmod.unsigned (N.v24129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24129 s i)) at 1.
  unfold R.v24129, N.v24129.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24130 (s : N.State) (i : N.Inputs) :
  R.v24130 (state s) (inputs i) = Zmod.unsigned (N.v24130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24130 s i)) at 1.
  unfold R.v24130, N.v24130.
  rewrite ?node_8957.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24131 (s : N.State) (i : N.Inputs) :
  R.v24131 (state s) (inputs i) = Zmod.unsigned (N.v24131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24131 s i)) at 1.
  unfold R.v24131, N.v24131.
  unfold R.v6, N.v6.
  rewrite !state_r842_nr_5F842.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r842_nr_5F842 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24132 (s : N.State) (i : N.Inputs) :
  R.v24132 (state s) (inputs i) = Zmod.unsigned (N.v24132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24132 s i)) at 1.
  unfold R.v24132, N.v24132.
  unfold R.v6, N.v6.
  rewrite ?node_8953.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24133 (s : N.State) (i : N.Inputs) :
  R.v24133 (state s) (inputs i) = Zmod.unsigned (N.v24133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24133 s i)) at 1.
  unfold R.v24133, N.v24133.
  rewrite ?node_24131.
  rewrite ?node_24132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24134 (s : N.State) (i : N.Inputs) :
  R.v24134 (state s) (inputs i) = Zmod.unsigned (N.v24134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24134 s i)) at 1.
  unfold R.v24134, N.v24134.
  unfold R.v16484, N.v16484.
  rewrite ?node_24133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24135 (s : N.State) (i : N.Inputs) :
  R.v24135 (state s) (inputs i) = Zmod.unsigned (N.v24135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24135 s i)) at 1.
  unfold R.v24135, N.v24135.
  rewrite ?node_24130.
  rewrite ?node_24134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24136 (s : N.State) (i : N.Inputs) :
  R.v24136 (state s) (inputs i) = Zmod.unsigned (N.v24136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24136 s i)) at 1.
  unfold R.v24136, N.v24136.
  unfold R.v6, N.v6.
  rewrite ?node_24135.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24137 (s : N.State) (i : N.Inputs) :
  R.v24137 (state s) (inputs i) = Zmod.unsigned (N.v24137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24137 s i)) at 1.
  unfold R.v24137, N.v24137.
  rewrite ?node_8958.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24138 (s : N.State) (i : N.Inputs) :
  R.v24138 (state s) (inputs i) = Zmod.unsigned (N.v24138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24138 s i)) at 1.
  unfold R.v24138, N.v24138.
  unfold R.v6, N.v6.
  rewrite ?node_9158.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24139 (s : N.State) (i : N.Inputs) :
  R.v24139 (state s) (inputs i) = Zmod.unsigned (N.v24139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24139 s i)) at 1.
  unfold R.v24139, N.v24139.
  rewrite ?node_24137.
  rewrite ?node_24138.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24140 (s : N.State) (i : N.Inputs) :
  R.v24140 (state s) (inputs i) = Zmod.unsigned (N.v24140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24140 s i)) at 1.
  unfold R.v24140, N.v24140.
  rewrite ?node_24136.
  rewrite ?node_24139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24141 (s : N.State) (i : N.Inputs) :
  R.v24141 (state s) (inputs i) = Zmod.unsigned (N.v24141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24141 s i)) at 1.
  unfold R.v24141, N.v24141.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24142 (s : N.State) (i : N.Inputs) :
  R.v24142 (state s) (inputs i) = Zmod.unsigned (N.v24142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24142 s i)) at 1.
  unfold R.v24142, N.v24142.
  rewrite ?node_8964.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24143 (s : N.State) (i : N.Inputs) :
  R.v24143 (state s) (inputs i) = Zmod.unsigned (N.v24143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24143 s i)) at 1.
  unfold R.v24143, N.v24143.
  unfold R.v16463, N.v16463.
  rewrite !state_r846_nr_5F846.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r846_nr_5F846 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24144 (s : N.State) (i : N.Inputs) :
  R.v24144 (state s) (inputs i) = Zmod.unsigned (N.v24144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24144 s i)) at 1.
  unfold R.v24144, N.v24144.
  unfold R.v16463, N.v16463.
  rewrite !state_r845_nr_5F845.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r845_nr_5F845 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24145 (s : N.State) (i : N.Inputs) :
  R.v24145 (state s) (inputs i) = Zmod.unsigned (N.v24145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24145 s i)) at 1.
  unfold R.v24145, N.v24145.
  unfold R.v6, N.v6.
  rewrite !state_r844_nr_5F844.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r844_nr_5F844 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24146 (s : N.State) (i : N.Inputs) :
  R.v24146 (state s) (inputs i) = Zmod.unsigned (N.v24146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24146 s i)) at 1.
  unfold R.v24146, N.v24146.
  unfold R.v6, N.v6.
  rewrite !state_r843_nr_5F843.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r843_nr_5F843 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24147 (s : N.State) (i : N.Inputs) :
  R.v24147 (state s) (inputs i) = Zmod.unsigned (N.v24147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24147 s i)) at 1.
  unfold R.v24147, N.v24147.
  rewrite ?node_24145.
  rewrite ?node_24146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24148 (s : N.State) (i : N.Inputs) :
  R.v24148 (state s) (inputs i) = Zmod.unsigned (N.v24148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24148 s i)) at 1.
  unfold R.v24148, N.v24148.
  unfold R.v16484, N.v16484.
  rewrite ?node_24147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24149 (s : N.State) (i : N.Inputs) :
  R.v24149 (state s) (inputs i) = Zmod.unsigned (N.v24149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24149 s i)) at 1.
  unfold R.v24149, N.v24149.
  rewrite ?node_24142.
  rewrite ?node_24143.
  rewrite ?node_24144.
  rewrite ?node_24148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24150 (s : N.State) (i : N.Inputs) :
  R.v24150 (state s) (inputs i) = Zmod.unsigned (N.v24150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24150 s i)) at 1.
  unfold R.v24150, N.v24150.
  unfold R.v6, N.v6.
  rewrite ?node_24149.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24151 (s : N.State) (i : N.Inputs) :
  R.v24151 (state s) (inputs i) = Zmod.unsigned (N.v24151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24151 s i)) at 1.
  unfold R.v24151, N.v24151.
  rewrite ?node_8965.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24152 (s : N.State) (i : N.Inputs) :
  R.v24152 (state s) (inputs i) = Zmod.unsigned (N.v24152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24152 s i)) at 1.
  unfold R.v24152, N.v24152.
  unfold R.v6, N.v6.
  rewrite ?node_9103.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24153 (s : N.State) (i : N.Inputs) :
  R.v24153 (state s) (inputs i) = Zmod.unsigned (N.v24153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24153 s i)) at 1.
  unfold R.v24153, N.v24153.
  unfold R.v6, N.v6.
  rewrite ?node_9161.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24154 (s : N.State) (i : N.Inputs) :
  R.v24154 (state s) (inputs i) = Zmod.unsigned (N.v24154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24154 s i)) at 1.
  unfold R.v24154, N.v24154.
  rewrite ?node_24151.
  rewrite ?node_24152.
  rewrite ?node_24153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24155 (s : N.State) (i : N.Inputs) :
  R.v24155 (state s) (inputs i) = Zmod.unsigned (N.v24155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24155 s i)) at 1.
  unfold R.v24155, N.v24155.
  rewrite ?node_24150.
  rewrite ?node_24154.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24156 (s : N.State) (i : N.Inputs) :
  R.v24156 (state s) (inputs i) = Zmod.unsigned (N.v24156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24156 s i)) at 1.
  unfold R.v24156, N.v24156.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24157 (s : N.State) (i : N.Inputs) :
  R.v24157 (state s) (inputs i) = Zmod.unsigned (N.v24157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24157 s i)) at 1.
  unfold R.v24157, N.v24157.
  unfold R.v16463, N.v16463.
  rewrite !state_r845_nr_5F845.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r845_nr_5F845 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24158 (s : N.State) (i : N.Inputs) :
  R.v24158 (state s) (inputs i) = Zmod.unsigned (N.v24158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24158 s i)) at 1.
  unfold R.v24158, N.v24158.
  unfold R.v6, N.v6.
  rewrite !state_r844_nr_5F844.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r844_nr_5F844 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24159 (s : N.State) (i : N.Inputs) :
  R.v24159 (state s) (inputs i) = Zmod.unsigned (N.v24159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24159 s i)) at 1.
  unfold R.v24159, N.v24159.
  unfold R.v6, N.v6.
  rewrite !state_r843_nr_5F843.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r843_nr_5F843 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24160 (s : N.State) (i : N.Inputs) :
  R.v24160 (state s) (inputs i) = Zmod.unsigned (N.v24160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24160 s i)) at 1.
  unfold R.v24160, N.v24160.
  rewrite ?node_24158.
  rewrite ?node_24159.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24161 (s : N.State) (i : N.Inputs) :
  R.v24161 (state s) (inputs i) = Zmod.unsigned (N.v24161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24161 s i)) at 1.
  unfold R.v24161, N.v24161.
  unfold R.v16484, N.v16484.
  rewrite ?node_24160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24162 (s : N.State) (i : N.Inputs) :
  R.v24162 (state s) (inputs i) = Zmod.unsigned (N.v24162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24162 s i)) at 1.
  unfold R.v24162, N.v24162.
  rewrite ?node_24157.
  rewrite ?node_24161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24163 (s : N.State) (i : N.Inputs) :
  R.v24163 (state s) (inputs i) = Zmod.unsigned (N.v24163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24163 s i)) at 1.
  unfold R.v24163, N.v24163.
  unfold R.v6, N.v6.
  rewrite ?node_24162.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24164 (s : N.State) (i : N.Inputs) :
  R.v24164 (state s) (inputs i) = Zmod.unsigned (N.v24164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24164 s i)) at 1.
  unfold R.v24164, N.v24164.
  rewrite ?node_8960.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24165 (s : N.State) (i : N.Inputs) :
  R.v24165 (state s) (inputs i) = Zmod.unsigned (N.v24165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24165 s i)) at 1.
  unfold R.v24165, N.v24165.
  unfold R.v6, N.v6.
  rewrite ?node_9103.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24166 (s : N.State) (i : N.Inputs) :
  R.v24166 (state s) (inputs i) = Zmod.unsigned (N.v24166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24166 s i)) at 1.
  unfold R.v24166, N.v24166.
  rewrite ?node_24164.
  rewrite ?node_24165.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24167 (s : N.State) (i : N.Inputs) :
  R.v24167 (state s) (inputs i) = Zmod.unsigned (N.v24167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24167 s i)) at 1.
  unfold R.v24167, N.v24167.
  rewrite ?node_24163.
  rewrite ?node_24166.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24168 (s : N.State) (i : N.Inputs) :
  R.v24168 (state s) (inputs i) = Zmod.unsigned (N.v24168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24168 s i)) at 1.
  unfold R.v24168, N.v24168.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24169 (s : N.State) (i : N.Inputs) :
  R.v24169 (state s) (inputs i) = Zmod.unsigned (N.v24169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24169 s i)) at 1.
  unfold R.v24169, N.v24169.
  rewrite ?node_8964.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24170 (s : N.State) (i : N.Inputs) :
  R.v24170 (state s) (inputs i) = Zmod.unsigned (N.v24170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24170 s i)) at 1.
  unfold R.v24170, N.v24170.
  unfold R.v6, N.v6.
  rewrite !state_r846_nr_5F846.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r846_nr_5F846 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24171 (s : N.State) (i : N.Inputs) :
  R.v24171 (state s) (inputs i) = Zmod.unsigned (N.v24171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24171 s i)) at 1.
  unfold R.v24171, N.v24171.
  unfold R.v6, N.v6.
  rewrite ?node_8960.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24172 (s : N.State) (i : N.Inputs) :
  R.v24172 (state s) (inputs i) = Zmod.unsigned (N.v24172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24172 s i)) at 1.
  unfold R.v24172, N.v24172.
  rewrite ?node_24170.
  rewrite ?node_24171.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24173 (s : N.State) (i : N.Inputs) :
  R.v24173 (state s) (inputs i) = Zmod.unsigned (N.v24173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24173 s i)) at 1.
  unfold R.v24173, N.v24173.
  unfold R.v16484, N.v16484.
  rewrite ?node_24172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24174 (s : N.State) (i : N.Inputs) :
  R.v24174 (state s) (inputs i) = Zmod.unsigned (N.v24174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24174 s i)) at 1.
  unfold R.v24174, N.v24174.
  rewrite ?node_24169.
  rewrite ?node_24173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24175 (s : N.State) (i : N.Inputs) :
  R.v24175 (state s) (inputs i) = Zmod.unsigned (N.v24175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24175 s i)) at 1.
  unfold R.v24175, N.v24175.
  unfold R.v6, N.v6.
  rewrite ?node_24174.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24176 (s : N.State) (i : N.Inputs) :
  R.v24176 (state s) (inputs i) = Zmod.unsigned (N.v24176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24176 s i)) at 1.
  unfold R.v24176, N.v24176.
  rewrite ?node_8965.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24177 (s : N.State) (i : N.Inputs) :
  R.v24177 (state s) (inputs i) = Zmod.unsigned (N.v24177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24177 s i)) at 1.
  unfold R.v24177, N.v24177.
  unfold R.v6, N.v6.
  rewrite ?node_9161.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24178 (s : N.State) (i : N.Inputs) :
  R.v24178 (state s) (inputs i) = Zmod.unsigned (N.v24178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24178 s i)) at 1.
  unfold R.v24178, N.v24178.
  rewrite ?node_24176.
  rewrite ?node_24177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24179 (s : N.State) (i : N.Inputs) :
  R.v24179 (state s) (inputs i) = Zmod.unsigned (N.v24179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24179 s i)) at 1.
  unfold R.v24179, N.v24179.
  rewrite ?node_24175.
  rewrite ?node_24178.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24180 (s : N.State) (i : N.Inputs) :
  R.v24180 (state s) (inputs i) = Zmod.unsigned (N.v24180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24180 s i)) at 1.
  unfold R.v24180, N.v24180.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24181 (s : N.State) (i : N.Inputs) :
  R.v24181 (state s) (inputs i) = Zmod.unsigned (N.v24181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24181 s i)) at 1.
  unfold R.v24181, N.v24181.
  rewrite ?node_8972.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24182 (s : N.State) (i : N.Inputs) :
  R.v24182 (state s) (inputs i) = Zmod.unsigned (N.v24182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24182 s i)) at 1.
  unfold R.v24182, N.v24182.
  unfold R.v16463, N.v16463.
  rewrite !state_r850_nr_5F850.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r850_nr_5F850 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24183 (s : N.State) (i : N.Inputs) :
  R.v24183 (state s) (inputs i) = Zmod.unsigned (N.v24183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24183 s i)) at 1.
  unfold R.v24183, N.v24183.
  unfold R.v16463, N.v16463.
  rewrite !state_r849_nr_5F849.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r849_nr_5F849 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24184 (s : N.State) (i : N.Inputs) :
  R.v24184 (state s) (inputs i) = Zmod.unsigned (N.v24184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24184 s i)) at 1.
  unfold R.v24184, N.v24184.
  unfold R.v6, N.v6.
  rewrite !state_r848_nr_5F848.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r848_nr_5F848 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24185 (s : N.State) (i : N.Inputs) :
  R.v24185 (state s) (inputs i) = Zmod.unsigned (N.v24185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24185 s i)) at 1.
  unfold R.v24185, N.v24185.
  unfold R.v6, N.v6.
  rewrite !state_r847_nr_5F847.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r847_nr_5F847 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24186 (s : N.State) (i : N.Inputs) :
  R.v24186 (state s) (inputs i) = Zmod.unsigned (N.v24186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24186 s i)) at 1.
  unfold R.v24186, N.v24186.
  rewrite ?node_24184.
  rewrite ?node_24185.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24187 (s : N.State) (i : N.Inputs) :
  R.v24187 (state s) (inputs i) = Zmod.unsigned (N.v24187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24187 s i)) at 1.
  unfold R.v24187, N.v24187.
  unfold R.v16484, N.v16484.
  rewrite ?node_24186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24188 (s : N.State) (i : N.Inputs) :
  R.v24188 (state s) (inputs i) = Zmod.unsigned (N.v24188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24188 s i)) at 1.
  unfold R.v24188, N.v24188.
  rewrite ?node_24181.
  rewrite ?node_24182.
  rewrite ?node_24183.
  rewrite ?node_24187.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24189 (s : N.State) (i : N.Inputs) :
  R.v24189 (state s) (inputs i) = Zmod.unsigned (N.v24189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24189 s i)) at 1.
  unfold R.v24189, N.v24189.
  unfold R.v6, N.v6.
  rewrite ?node_24188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24190 (s : N.State) (i : N.Inputs) :
  R.v24190 (state s) (inputs i) = Zmod.unsigned (N.v24190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24190 s i)) at 1.
  unfold R.v24190, N.v24190.
  rewrite ?node_8973.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24191 (s : N.State) (i : N.Inputs) :
  R.v24191 (state s) (inputs i) = Zmod.unsigned (N.v24191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24191 s i)) at 1.
  unfold R.v24191, N.v24191.
  unfold R.v6, N.v6.
  rewrite ?node_9111.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24192 (s : N.State) (i : N.Inputs) :
  R.v24192 (state s) (inputs i) = Zmod.unsigned (N.v24192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24192 s i)) at 1.
  unfold R.v24192, N.v24192.
  unfold R.v6, N.v6.
  rewrite ?node_9165.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24193 (s : N.State) (i : N.Inputs) :
  R.v24193 (state s) (inputs i) = Zmod.unsigned (N.v24193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24193 s i)) at 1.
  unfold R.v24193, N.v24193.
  rewrite ?node_24190.
  rewrite ?node_24191.
  rewrite ?node_24192.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24194 (s : N.State) (i : N.Inputs) :
  R.v24194 (state s) (inputs i) = Zmod.unsigned (N.v24194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24194 s i)) at 1.
  unfold R.v24194, N.v24194.
  rewrite ?node_24189.
  rewrite ?node_24193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24195 (s : N.State) (i : N.Inputs) :
  R.v24195 (state s) (inputs i) = Zmod.unsigned (N.v24195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24195 s i)) at 1.
  unfold R.v24195, N.v24195.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24196 (s : N.State) (i : N.Inputs) :
  R.v24196 (state s) (inputs i) = Zmod.unsigned (N.v24196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24196 s i)) at 1.
  unfold R.v24196, N.v24196.
  unfold R.v16463, N.v16463.
  rewrite !state_r849_nr_5F849.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r849_nr_5F849 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24197 (s : N.State) (i : N.Inputs) :
  R.v24197 (state s) (inputs i) = Zmod.unsigned (N.v24197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24197 s i)) at 1.
  unfold R.v24197, N.v24197.
  unfold R.v6, N.v6.
  rewrite !state_r848_nr_5F848.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r848_nr_5F848 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24198 (s : N.State) (i : N.Inputs) :
  R.v24198 (state s) (inputs i) = Zmod.unsigned (N.v24198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24198 s i)) at 1.
  unfold R.v24198, N.v24198.
  unfold R.v6, N.v6.
  rewrite !state_r847_nr_5F847.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r847_nr_5F847 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24199 (s : N.State) (i : N.Inputs) :
  R.v24199 (state s) (inputs i) = Zmod.unsigned (N.v24199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24199 s i)) at 1.
  unfold R.v24199, N.v24199.
  rewrite ?node_24197.
  rewrite ?node_24198.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24200 (s : N.State) (i : N.Inputs) :
  R.v24200 (state s) (inputs i) = Zmod.unsigned (N.v24200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24200 s i)) at 1.
  unfold R.v24200, N.v24200.
  unfold R.v16484, N.v16484.
  rewrite ?node_24199.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24201 (s : N.State) (i : N.Inputs) :
  R.v24201 (state s) (inputs i) = Zmod.unsigned (N.v24201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24201 s i)) at 1.
  unfold R.v24201, N.v24201.
  rewrite ?node_24196.
  rewrite ?node_24200.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24202 (s : N.State) (i : N.Inputs) :
  R.v24202 (state s) (inputs i) = Zmod.unsigned (N.v24202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24202 s i)) at 1.
  unfold R.v24202, N.v24202.
  unfold R.v6, N.v6.
  rewrite ?node_24201.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24203 (s : N.State) (i : N.Inputs) :
  R.v24203 (state s) (inputs i) = Zmod.unsigned (N.v24203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24203 s i)) at 1.
  unfold R.v24203, N.v24203.
  rewrite ?node_8968.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24204 (s : N.State) (i : N.Inputs) :
  R.v24204 (state s) (inputs i) = Zmod.unsigned (N.v24204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24204 s i)) at 1.
  unfold R.v24204, N.v24204.
  unfold R.v6, N.v6.
  rewrite ?node_9111.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24205 (s : N.State) (i : N.Inputs) :
  R.v24205 (state s) (inputs i) = Zmod.unsigned (N.v24205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24205 s i)) at 1.
  unfold R.v24205, N.v24205.
  rewrite ?node_24203.
  rewrite ?node_24204.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24206 (s : N.State) (i : N.Inputs) :
  R.v24206 (state s) (inputs i) = Zmod.unsigned (N.v24206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24206 s i)) at 1.
  unfold R.v24206, N.v24206.
  rewrite ?node_24202.
  rewrite ?node_24205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24207 (s : N.State) (i : N.Inputs) :
  R.v24207 (state s) (inputs i) = Zmod.unsigned (N.v24207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24207 s i)) at 1.
  unfold R.v24207, N.v24207.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24208 (s : N.State) (i : N.Inputs) :
  R.v24208 (state s) (inputs i) = Zmod.unsigned (N.v24208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24208 s i)) at 1.
  unfold R.v24208, N.v24208.
  rewrite ?node_8972.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24209 (s : N.State) (i : N.Inputs) :
  R.v24209 (state s) (inputs i) = Zmod.unsigned (N.v24209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24209 s i)) at 1.
  unfold R.v24209, N.v24209.
  unfold R.v6, N.v6.
  rewrite !state_r850_nr_5F850.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r850_nr_5F850 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24210 (s : N.State) (i : N.Inputs) :
  R.v24210 (state s) (inputs i) = Zmod.unsigned (N.v24210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24210 s i)) at 1.
  unfold R.v24210, N.v24210.
  unfold R.v6, N.v6.
  rewrite ?node_8968.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24211 (s : N.State) (i : N.Inputs) :
  R.v24211 (state s) (inputs i) = Zmod.unsigned (N.v24211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24211 s i)) at 1.
  unfold R.v24211, N.v24211.
  rewrite ?node_24209.
  rewrite ?node_24210.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24212 (s : N.State) (i : N.Inputs) :
  R.v24212 (state s) (inputs i) = Zmod.unsigned (N.v24212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24212 s i)) at 1.
  unfold R.v24212, N.v24212.
  unfold R.v16484, N.v16484.
  rewrite ?node_24211.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24213 (s : N.State) (i : N.Inputs) :
  R.v24213 (state s) (inputs i) = Zmod.unsigned (N.v24213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24213 s i)) at 1.
  unfold R.v24213, N.v24213.
  rewrite ?node_24208.
  rewrite ?node_24212.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24214 (s : N.State) (i : N.Inputs) :
  R.v24214 (state s) (inputs i) = Zmod.unsigned (N.v24214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24214 s i)) at 1.
  unfold R.v24214, N.v24214.
  unfold R.v6, N.v6.
  rewrite ?node_24213.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24215 (s : N.State) (i : N.Inputs) :
  R.v24215 (state s) (inputs i) = Zmod.unsigned (N.v24215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24215 s i)) at 1.
  unfold R.v24215, N.v24215.
  rewrite ?node_8973.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24216 (s : N.State) (i : N.Inputs) :
  R.v24216 (state s) (inputs i) = Zmod.unsigned (N.v24216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24216 s i)) at 1.
  unfold R.v24216, N.v24216.
  unfold R.v6, N.v6.
  rewrite ?node_9165.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24217 (s : N.State) (i : N.Inputs) :
  R.v24217 (state s) (inputs i) = Zmod.unsigned (N.v24217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24217 s i)) at 1.
  unfold R.v24217, N.v24217.
  rewrite ?node_24215.
  rewrite ?node_24216.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24218 (s : N.State) (i : N.Inputs) :
  R.v24218 (state s) (inputs i) = Zmod.unsigned (N.v24218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24218 s i)) at 1.
  unfold R.v24218, N.v24218.
  rewrite ?node_24214.
  rewrite ?node_24217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24219 (s : N.State) (i : N.Inputs) :
  R.v24219 (state s) (inputs i) = Zmod.unsigned (N.v24219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24219 s i)) at 1.
  unfold R.v24219, N.v24219.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24220 (s : N.State) (i : N.Inputs) :
  R.v24220 (state s) (inputs i) = Zmod.unsigned (N.v24220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24220 s i)) at 1.
  unfold R.v24220, N.v24220.
  rewrite ?node_8980.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24221 (s : N.State) (i : N.Inputs) :
  R.v24221 (state s) (inputs i) = Zmod.unsigned (N.v24221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24221 s i)) at 1.
  unfold R.v24221, N.v24221.
  unfold R.v16463, N.v16463.
  rewrite !state_r854_nr_5F854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r854_nr_5F854 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24222 (s : N.State) (i : N.Inputs) :
  R.v24222 (state s) (inputs i) = Zmod.unsigned (N.v24222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24222 s i)) at 1.
  unfold R.v24222, N.v24222.
  unfold R.v16463, N.v16463.
  rewrite !state_r853_nr_5F853.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r853_nr_5F853 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24223 (s : N.State) (i : N.Inputs) :
  R.v24223 (state s) (inputs i) = Zmod.unsigned (N.v24223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24223 s i)) at 1.
  unfold R.v24223, N.v24223.
  unfold R.v6, N.v6.
  rewrite !state_r852_nr_5F852.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r852_nr_5F852 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24224 (s : N.State) (i : N.Inputs) :
  R.v24224 (state s) (inputs i) = Zmod.unsigned (N.v24224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24224 s i)) at 1.
  unfold R.v24224, N.v24224.
  unfold R.v6, N.v6.
  rewrite !state_r851_nr_5F851.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r851_nr_5F851 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24225 (s : N.State) (i : N.Inputs) :
  R.v24225 (state s) (inputs i) = Zmod.unsigned (N.v24225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24225 s i)) at 1.
  unfold R.v24225, N.v24225.
  rewrite ?node_24223.
  rewrite ?node_24224.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24226 (s : N.State) (i : N.Inputs) :
  R.v24226 (state s) (inputs i) = Zmod.unsigned (N.v24226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24226 s i)) at 1.
  unfold R.v24226, N.v24226.
  unfold R.v16484, N.v16484.
  rewrite ?node_24225.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24227 (s : N.State) (i : N.Inputs) :
  R.v24227 (state s) (inputs i) = Zmod.unsigned (N.v24227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24227 s i)) at 1.
  unfold R.v24227, N.v24227.
  rewrite ?node_24220.
  rewrite ?node_24221.
  rewrite ?node_24222.
  rewrite ?node_24226.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24228 (s : N.State) (i : N.Inputs) :
  R.v24228 (state s) (inputs i) = Zmod.unsigned (N.v24228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24228 s i)) at 1.
  unfold R.v24228, N.v24228.
  unfold R.v6, N.v6.
  rewrite ?node_24227.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24229 (s : N.State) (i : N.Inputs) :
  R.v24229 (state s) (inputs i) = Zmod.unsigned (N.v24229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24229 s i)) at 1.
  unfold R.v24229, N.v24229.
  rewrite ?node_8981.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24230 (s : N.State) (i : N.Inputs) :
  R.v24230 (state s) (inputs i) = Zmod.unsigned (N.v24230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24230 s i)) at 1.
  unfold R.v24230, N.v24230.
  unfold R.v6, N.v6.
  rewrite ?node_9119.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24231 (s : N.State) (i : N.Inputs) :
  R.v24231 (state s) (inputs i) = Zmod.unsigned (N.v24231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24231 s i)) at 1.
  unfold R.v24231, N.v24231.
  unfold R.v6, N.v6.
  rewrite ?node_9169.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24232 (s : N.State) (i : N.Inputs) :
  R.v24232 (state s) (inputs i) = Zmod.unsigned (N.v24232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24232 s i)) at 1.
  unfold R.v24232, N.v24232.
  rewrite ?node_24229.
  rewrite ?node_24230.
  rewrite ?node_24231.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24233 (s : N.State) (i : N.Inputs) :
  R.v24233 (state s) (inputs i) = Zmod.unsigned (N.v24233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24233 s i)) at 1.
  unfold R.v24233, N.v24233.
  rewrite ?node_24228.
  rewrite ?node_24232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24234 (s : N.State) (i : N.Inputs) :
  R.v24234 (state s) (inputs i) = Zmod.unsigned (N.v24234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24234 s i)) at 1.
  unfold R.v24234, N.v24234.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24235 (s : N.State) (i : N.Inputs) :
  R.v24235 (state s) (inputs i) = Zmod.unsigned (N.v24235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24235 s i)) at 1.
  unfold R.v24235, N.v24235.
  unfold R.v16463, N.v16463.
  rewrite !state_r853_nr_5F853.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r853_nr_5F853 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24236 (s : N.State) (i : N.Inputs) :
  R.v24236 (state s) (inputs i) = Zmod.unsigned (N.v24236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24236 s i)) at 1.
  unfold R.v24236, N.v24236.
  unfold R.v6, N.v6.
  rewrite !state_r852_nr_5F852.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r852_nr_5F852 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24237 (s : N.State) (i : N.Inputs) :
  R.v24237 (state s) (inputs i) = Zmod.unsigned (N.v24237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24237 s i)) at 1.
  unfold R.v24237, N.v24237.
  unfold R.v6, N.v6.
  rewrite !state_r851_nr_5F851.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r851_nr_5F851 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24238 (s : N.State) (i : N.Inputs) :
  R.v24238 (state s) (inputs i) = Zmod.unsigned (N.v24238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24238 s i)) at 1.
  unfold R.v24238, N.v24238.
  rewrite ?node_24236.
  rewrite ?node_24237.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24239 (s : N.State) (i : N.Inputs) :
  R.v24239 (state s) (inputs i) = Zmod.unsigned (N.v24239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24239 s i)) at 1.
  unfold R.v24239, N.v24239.
  unfold R.v16484, N.v16484.
  rewrite ?node_24238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24240 (s : N.State) (i : N.Inputs) :
  R.v24240 (state s) (inputs i) = Zmod.unsigned (N.v24240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24240 s i)) at 1.
  unfold R.v24240, N.v24240.
  rewrite ?node_24235.
  rewrite ?node_24239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24241 (s : N.State) (i : N.Inputs) :
  R.v24241 (state s) (inputs i) = Zmod.unsigned (N.v24241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24241 s i)) at 1.
  unfold R.v24241, N.v24241.
  unfold R.v6, N.v6.
  rewrite ?node_24240.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24242 (s : N.State) (i : N.Inputs) :
  R.v24242 (state s) (inputs i) = Zmod.unsigned (N.v24242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24242 s i)) at 1.
  unfold R.v24242, N.v24242.
  rewrite ?node_8976.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24243 (s : N.State) (i : N.Inputs) :
  R.v24243 (state s) (inputs i) = Zmod.unsigned (N.v24243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24243 s i)) at 1.
  unfold R.v24243, N.v24243.
  unfold R.v6, N.v6.
  rewrite ?node_9119.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24244 (s : N.State) (i : N.Inputs) :
  R.v24244 (state s) (inputs i) = Zmod.unsigned (N.v24244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24244 s i)) at 1.
  unfold R.v24244, N.v24244.
  rewrite ?node_24242.
  rewrite ?node_24243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24245 (s : N.State) (i : N.Inputs) :
  R.v24245 (state s) (inputs i) = Zmod.unsigned (N.v24245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24245 s i)) at 1.
  unfold R.v24245, N.v24245.
  rewrite ?node_24241.
  rewrite ?node_24244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24246 (s : N.State) (i : N.Inputs) :
  R.v24246 (state s) (inputs i) = Zmod.unsigned (N.v24246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24246 s i)) at 1.
  unfold R.v24246, N.v24246.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24247 (s : N.State) (i : N.Inputs) :
  R.v24247 (state s) (inputs i) = Zmod.unsigned (N.v24247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24247 s i)) at 1.
  unfold R.v24247, N.v24247.
  rewrite ?node_8980.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24248 (s : N.State) (i : N.Inputs) :
  R.v24248 (state s) (inputs i) = Zmod.unsigned (N.v24248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24248 s i)) at 1.
  unfold R.v24248, N.v24248.
  unfold R.v6, N.v6.
  rewrite !state_r854_nr_5F854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r854_nr_5F854 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24249 (s : N.State) (i : N.Inputs) :
  R.v24249 (state s) (inputs i) = Zmod.unsigned (N.v24249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24249 s i)) at 1.
  unfold R.v24249, N.v24249.
  unfold R.v6, N.v6.
  rewrite ?node_8976.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24250 (s : N.State) (i : N.Inputs) :
  R.v24250 (state s) (inputs i) = Zmod.unsigned (N.v24250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24250 s i)) at 1.
  unfold R.v24250, N.v24250.
  rewrite ?node_24248.
  rewrite ?node_24249.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24251 (s : N.State) (i : N.Inputs) :
  R.v24251 (state s) (inputs i) = Zmod.unsigned (N.v24251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24251 s i)) at 1.
  unfold R.v24251, N.v24251.
  unfold R.v16484, N.v16484.
  rewrite ?node_24250.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24252 (s : N.State) (i : N.Inputs) :
  R.v24252 (state s) (inputs i) = Zmod.unsigned (N.v24252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24252 s i)) at 1.
  unfold R.v24252, N.v24252.
  rewrite ?node_24247.
  rewrite ?node_24251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24253 (s : N.State) (i : N.Inputs) :
  R.v24253 (state s) (inputs i) = Zmod.unsigned (N.v24253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24253 s i)) at 1.
  unfold R.v24253, N.v24253.
  unfold R.v6, N.v6.
  rewrite ?node_24252.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24254 (s : N.State) (i : N.Inputs) :
  R.v24254 (state s) (inputs i) = Zmod.unsigned (N.v24254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24254 s i)) at 1.
  unfold R.v24254, N.v24254.
  rewrite ?node_8981.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24255 (s : N.State) (i : N.Inputs) :
  R.v24255 (state s) (inputs i) = Zmod.unsigned (N.v24255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24255 s i)) at 1.
  unfold R.v24255, N.v24255.
  unfold R.v6, N.v6.
  rewrite ?node_9169.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24256 (s : N.State) (i : N.Inputs) :
  R.v24256 (state s) (inputs i) = Zmod.unsigned (N.v24256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24256 s i)) at 1.
  unfold R.v24256, N.v24256.
  rewrite ?node_24254.
  rewrite ?node_24255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24257 (s : N.State) (i : N.Inputs) :
  R.v24257 (state s) (inputs i) = Zmod.unsigned (N.v24257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24257 s i)) at 1.
  unfold R.v24257, N.v24257.
  rewrite ?node_24253.
  rewrite ?node_24256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24258 (s : N.State) (i : N.Inputs) :
  R.v24258 (state s) (inputs i) = Zmod.unsigned (N.v24258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24258 s i)) at 1.
  unfold R.v24258, N.v24258.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24259 (s : N.State) (i : N.Inputs) :
  R.v24259 (state s) (inputs i) = Zmod.unsigned (N.v24259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24259 s i)) at 1.
  unfold R.v24259, N.v24259.
  rewrite ?node_8992.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24260 (s : N.State) (i : N.Inputs) :
  R.v24260 (state s) (inputs i) = Zmod.unsigned (N.v24260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24260 s i)) at 1.
  unfold R.v24260, N.v24260.
  unfold R.v16463, N.v16463.
  rewrite !state_r858_nr_5F858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r858_nr_5F858 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24261 (s : N.State) (i : N.Inputs) :
  R.v24261 (state s) (inputs i) = Zmod.unsigned (N.v24261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24261 s i)) at 1.
  unfold R.v24261, N.v24261.
  unfold R.v16463, N.v16463.
  rewrite !state_r857_nr_5F857.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r857_nr_5F857 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24262 (s : N.State) (i : N.Inputs) :
  R.v24262 (state s) (inputs i) = Zmod.unsigned (N.v24262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24262 s i)) at 1.
  unfold R.v24262, N.v24262.
  unfold R.v6, N.v6.
  rewrite !state_r856_nr_5F856.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r856_nr_5F856 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24263 (s : N.State) (i : N.Inputs) :
  R.v24263 (state s) (inputs i) = Zmod.unsigned (N.v24263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24263 s i)) at 1.
  unfold R.v24263, N.v24263.
  unfold R.v6, N.v6.
  rewrite !state_r855_nr_5F855.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r855_nr_5F855 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24264 (s : N.State) (i : N.Inputs) :
  R.v24264 (state s) (inputs i) = Zmod.unsigned (N.v24264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24264 s i)) at 1.
  unfold R.v24264, N.v24264.
  rewrite ?node_24262.
  rewrite ?node_24263.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24265 (s : N.State) (i : N.Inputs) :
  R.v24265 (state s) (inputs i) = Zmod.unsigned (N.v24265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24265 s i)) at 1.
  unfold R.v24265, N.v24265.
  unfold R.v16484, N.v16484.
  rewrite ?node_24264.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24266 (s : N.State) (i : N.Inputs) :
  R.v24266 (state s) (inputs i) = Zmod.unsigned (N.v24266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24266 s i)) at 1.
  unfold R.v24266, N.v24266.
  rewrite ?node_24259.
  rewrite ?node_24260.
  rewrite ?node_24261.
  rewrite ?node_24265.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24267 (s : N.State) (i : N.Inputs) :
  R.v24267 (state s) (inputs i) = Zmod.unsigned (N.v24267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24267 s i)) at 1.
  unfold R.v24267, N.v24267.
  unfold R.v6, N.v6.
  rewrite ?node_24266.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24268 (s : N.State) (i : N.Inputs) :
  R.v24268 (state s) (inputs i) = Zmod.unsigned (N.v24268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24268 s i)) at 1.
  unfold R.v24268, N.v24268.
  rewrite ?node_8993.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24269 (s : N.State) (i : N.Inputs) :
  R.v24269 (state s) (inputs i) = Zmod.unsigned (N.v24269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24269 s i)) at 1.
  unfold R.v24269, N.v24269.
  unfold R.v6, N.v6.
  rewrite ?node_9131.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24270 (s : N.State) (i : N.Inputs) :
  R.v24270 (state s) (inputs i) = Zmod.unsigned (N.v24270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24270 s i)) at 1.
  unfold R.v24270, N.v24270.
  unfold R.v6, N.v6.
  rewrite ?node_9178.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24271 (s : N.State) (i : N.Inputs) :
  R.v24271 (state s) (inputs i) = Zmod.unsigned (N.v24271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24271 s i)) at 1.
  unfold R.v24271, N.v24271.
  rewrite ?node_24268.
  rewrite ?node_24269.
  rewrite ?node_24270.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24272 (s : N.State) (i : N.Inputs) :
  R.v24272 (state s) (inputs i) = Zmod.unsigned (N.v24272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24272 s i)) at 1.
  unfold R.v24272, N.v24272.
  rewrite ?node_24267.
  rewrite ?node_24271.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24273 (s : N.State) (i : N.Inputs) :
  R.v24273 (state s) (inputs i) = Zmod.unsigned (N.v24273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24273 s i)) at 1.
  unfold R.v24273, N.v24273.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24274 (s : N.State) (i : N.Inputs) :
  R.v24274 (state s) (inputs i) = Zmod.unsigned (N.v24274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24274 s i)) at 1.
  unfold R.v24274, N.v24274.
  unfold R.v16463, N.v16463.
  rewrite !state_r857_nr_5F857.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r857_nr_5F857 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24275 (s : N.State) (i : N.Inputs) :
  R.v24275 (state s) (inputs i) = Zmod.unsigned (N.v24275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24275 s i)) at 1.
  unfold R.v24275, N.v24275.
  unfold R.v6, N.v6.
  rewrite !state_r856_nr_5F856.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r856_nr_5F856 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24276 (s : N.State) (i : N.Inputs) :
  R.v24276 (state s) (inputs i) = Zmod.unsigned (N.v24276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24276 s i)) at 1.
  unfold R.v24276, N.v24276.
  unfold R.v6, N.v6.
  rewrite !state_r855_nr_5F855.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r855_nr_5F855 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24277 (s : N.State) (i : N.Inputs) :
  R.v24277 (state s) (inputs i) = Zmod.unsigned (N.v24277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24277 s i)) at 1.
  unfold R.v24277, N.v24277.
  rewrite ?node_24275.
  rewrite ?node_24276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24278 (s : N.State) (i : N.Inputs) :
  R.v24278 (state s) (inputs i) = Zmod.unsigned (N.v24278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24278 s i)) at 1.
  unfold R.v24278, N.v24278.
  unfold R.v16484, N.v16484.
  rewrite ?node_24277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24279 (s : N.State) (i : N.Inputs) :
  R.v24279 (state s) (inputs i) = Zmod.unsigned (N.v24279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24279 s i)) at 1.
  unfold R.v24279, N.v24279.
  rewrite ?node_24274.
  rewrite ?node_24278.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24280 (s : N.State) (i : N.Inputs) :
  R.v24280 (state s) (inputs i) = Zmod.unsigned (N.v24280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24280 s i)) at 1.
  unfold R.v24280, N.v24280.
  unfold R.v6, N.v6.
  rewrite ?node_24279.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24281 (s : N.State) (i : N.Inputs) :
  R.v24281 (state s) (inputs i) = Zmod.unsigned (N.v24281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24281 s i)) at 1.
  unfold R.v24281, N.v24281.
  rewrite ?node_8988.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24282 (s : N.State) (i : N.Inputs) :
  R.v24282 (state s) (inputs i) = Zmod.unsigned (N.v24282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24282 s i)) at 1.
  unfold R.v24282, N.v24282.
  unfold R.v6, N.v6.
  rewrite ?node_9131.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24283 (s : N.State) (i : N.Inputs) :
  R.v24283 (state s) (inputs i) = Zmod.unsigned (N.v24283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24283 s i)) at 1.
  unfold R.v24283, N.v24283.
  rewrite ?node_24281.
  rewrite ?node_24282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24284 (s : N.State) (i : N.Inputs) :
  R.v24284 (state s) (inputs i) = Zmod.unsigned (N.v24284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24284 s i)) at 1.
  unfold R.v24284, N.v24284.
  rewrite ?node_24280.
  rewrite ?node_24283.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24285 (s : N.State) (i : N.Inputs) :
  R.v24285 (state s) (inputs i) = Zmod.unsigned (N.v24285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24285 s i)) at 1.
  unfold R.v24285, N.v24285.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24286 (s : N.State) (i : N.Inputs) :
  R.v24286 (state s) (inputs i) = Zmod.unsigned (N.v24286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24286 s i)) at 1.
  unfold R.v24286, N.v24286.
  rewrite ?node_8992.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24287 (s : N.State) (i : N.Inputs) :
  R.v24287 (state s) (inputs i) = Zmod.unsigned (N.v24287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24287 s i)) at 1.
  unfold R.v24287, N.v24287.
  unfold R.v6, N.v6.
  rewrite !state_r858_nr_5F858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r858_nr_5F858 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24288 (s : N.State) (i : N.Inputs) :
  R.v24288 (state s) (inputs i) = Zmod.unsigned (N.v24288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24288 s i)) at 1.
  unfold R.v24288, N.v24288.
  unfold R.v6, N.v6.
  rewrite ?node_8988.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24289 (s : N.State) (i : N.Inputs) :
  R.v24289 (state s) (inputs i) = Zmod.unsigned (N.v24289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24289 s i)) at 1.
  unfold R.v24289, N.v24289.
  rewrite ?node_24287.
  rewrite ?node_24288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24290 (s : N.State) (i : N.Inputs) :
  R.v24290 (state s) (inputs i) = Zmod.unsigned (N.v24290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24290 s i)) at 1.
  unfold R.v24290, N.v24290.
  unfold R.v16484, N.v16484.
  rewrite ?node_24289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24291 (s : N.State) (i : N.Inputs) :
  R.v24291 (state s) (inputs i) = Zmod.unsigned (N.v24291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24291 s i)) at 1.
  unfold R.v24291, N.v24291.
  rewrite ?node_24286.
  rewrite ?node_24290.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24292 (s : N.State) (i : N.Inputs) :
  R.v24292 (state s) (inputs i) = Zmod.unsigned (N.v24292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24292 s i)) at 1.
  unfold R.v24292, N.v24292.
  unfold R.v6, N.v6.
  rewrite ?node_24291.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24293 (s : N.State) (i : N.Inputs) :
  R.v24293 (state s) (inputs i) = Zmod.unsigned (N.v24293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24293 s i)) at 1.
  unfold R.v24293, N.v24293.
  rewrite ?node_8993.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24294 (s : N.State) (i : N.Inputs) :
  R.v24294 (state s) (inputs i) = Zmod.unsigned (N.v24294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24294 s i)) at 1.
  unfold R.v24294, N.v24294.
  unfold R.v6, N.v6.
  rewrite ?node_9178.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24295 (s : N.State) (i : N.Inputs) :
  R.v24295 (state s) (inputs i) = Zmod.unsigned (N.v24295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24295 s i)) at 1.
  unfold R.v24295, N.v24295.
  rewrite ?node_24293.
  rewrite ?node_24294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24296 (s : N.State) (i : N.Inputs) :
  R.v24296 (state s) (inputs i) = Zmod.unsigned (N.v24296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24296 s i)) at 1.
  unfold R.v24296, N.v24296.
  rewrite ?node_24292.
  rewrite ?node_24295.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24297 (s : N.State) (i : N.Inputs) :
  R.v24297 (state s) (inputs i) = Zmod.unsigned (N.v24297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24297 s i)) at 1.
  unfold R.v24297, N.v24297.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24298 (s : N.State) (i : N.Inputs) :
  R.v24298 (state s) (inputs i) = Zmod.unsigned (N.v24298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24298 s i)) at 1.
  unfold R.v24298, N.v24298.
  rewrite ?node_8999.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24299 (s : N.State) (i : N.Inputs) :
  R.v24299 (state s) (inputs i) = Zmod.unsigned (N.v24299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24299 s i)) at 1.
  unfold R.v24299, N.v24299.
  unfold R.v16463, N.v16463.
  rewrite !state_r862_nr_5F862.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r862_nr_5F862 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24300 (s : N.State) (i : N.Inputs) :
  R.v24300 (state s) (inputs i) = Zmod.unsigned (N.v24300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24300 s i)) at 1.
  unfold R.v24300, N.v24300.
  unfold R.v16463, N.v16463.
  rewrite !state_r861_nr_5F861.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r861_nr_5F861 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24301 (s : N.State) (i : N.Inputs) :
  R.v24301 (state s) (inputs i) = Zmod.unsigned (N.v24301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24301 s i)) at 1.
  unfold R.v24301, N.v24301.
  unfold R.v6, N.v6.
  rewrite !state_r860_nr_5F860.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r860_nr_5F860 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24302 (s : N.State) (i : N.Inputs) :
  R.v24302 (state s) (inputs i) = Zmod.unsigned (N.v24302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24302 s i)) at 1.
  unfold R.v24302, N.v24302.
  unfold R.v6, N.v6.
  rewrite !state_r859_nr_5F859.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r859_nr_5F859 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24303 (s : N.State) (i : N.Inputs) :
  R.v24303 (state s) (inputs i) = Zmod.unsigned (N.v24303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24303 s i)) at 1.
  unfold R.v24303, N.v24303.
  rewrite ?node_24301.
  rewrite ?node_24302.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24304 (s : N.State) (i : N.Inputs) :
  R.v24304 (state s) (inputs i) = Zmod.unsigned (N.v24304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24304 s i)) at 1.
  unfold R.v24304, N.v24304.
  unfold R.v16484, N.v16484.
  rewrite ?node_24303.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24305 (s : N.State) (i : N.Inputs) :
  R.v24305 (state s) (inputs i) = Zmod.unsigned (N.v24305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24305 s i)) at 1.
  unfold R.v24305, N.v24305.
  rewrite ?node_24298.
  rewrite ?node_24299.
  rewrite ?node_24300.
  rewrite ?node_24304.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24306 (s : N.State) (i : N.Inputs) :
  R.v24306 (state s) (inputs i) = Zmod.unsigned (N.v24306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24306 s i)) at 1.
  unfold R.v24306, N.v24306.
  unfold R.v6, N.v6.
  rewrite ?node_24305.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24307 (s : N.State) (i : N.Inputs) :
  R.v24307 (state s) (inputs i) = Zmod.unsigned (N.v24307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24307 s i)) at 1.
  unfold R.v24307, N.v24307.
  rewrite ?node_9000.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24308 (s : N.State) (i : N.Inputs) :
  R.v24308 (state s) (inputs i) = Zmod.unsigned (N.v24308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24308 s i)) at 1.
  unfold R.v24308, N.v24308.
  unfold R.v6, N.v6.
  rewrite ?node_9138.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24309 (s : N.State) (i : N.Inputs) :
  R.v24309 (state s) (inputs i) = Zmod.unsigned (N.v24309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24309 s i)) at 1.
  unfold R.v24309, N.v24309.
  unfold R.v6, N.v6.
  rewrite ?node_9181.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24310 (s : N.State) (i : N.Inputs) :
  R.v24310 (state s) (inputs i) = Zmod.unsigned (N.v24310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24310 s i)) at 1.
  unfold R.v24310, N.v24310.
  rewrite ?node_24307.
  rewrite ?node_24308.
  rewrite ?node_24309.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24311 (s : N.State) (i : N.Inputs) :
  R.v24311 (state s) (inputs i) = Zmod.unsigned (N.v24311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24311 s i)) at 1.
  unfold R.v24311, N.v24311.
  rewrite ?node_24306.
  rewrite ?node_24310.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24312 (s : N.State) (i : N.Inputs) :
  R.v24312 (state s) (inputs i) = Zmod.unsigned (N.v24312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24312 s i)) at 1.
  unfold R.v24312, N.v24312.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24313 (s : N.State) (i : N.Inputs) :
  R.v24313 (state s) (inputs i) = Zmod.unsigned (N.v24313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24313 s i)) at 1.
  unfold R.v24313, N.v24313.
  unfold R.v16463, N.v16463.
  rewrite !state_r861_nr_5F861.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r861_nr_5F861 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24314 (s : N.State) (i : N.Inputs) :
  R.v24314 (state s) (inputs i) = Zmod.unsigned (N.v24314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24314 s i)) at 1.
  unfold R.v24314, N.v24314.
  unfold R.v6, N.v6.
  rewrite !state_r860_nr_5F860.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r860_nr_5F860 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24315 (s : N.State) (i : N.Inputs) :
  R.v24315 (state s) (inputs i) = Zmod.unsigned (N.v24315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24315 s i)) at 1.
  unfold R.v24315, N.v24315.
  unfold R.v6, N.v6.
  rewrite !state_r859_nr_5F859.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r859_nr_5F859 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24316 (s : N.State) (i : N.Inputs) :
  R.v24316 (state s) (inputs i) = Zmod.unsigned (N.v24316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24316 s i)) at 1.
  unfold R.v24316, N.v24316.
  rewrite ?node_24314.
  rewrite ?node_24315.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24317 (s : N.State) (i : N.Inputs) :
  R.v24317 (state s) (inputs i) = Zmod.unsigned (N.v24317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24317 s i)) at 1.
  unfold R.v24317, N.v24317.
  unfold R.v16484, N.v16484.
  rewrite ?node_24316.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24318 (s : N.State) (i : N.Inputs) :
  R.v24318 (state s) (inputs i) = Zmod.unsigned (N.v24318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24318 s i)) at 1.
  unfold R.v24318, N.v24318.
  rewrite ?node_24313.
  rewrite ?node_24317.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24319 (s : N.State) (i : N.Inputs) :
  R.v24319 (state s) (inputs i) = Zmod.unsigned (N.v24319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24319 s i)) at 1.
  unfold R.v24319, N.v24319.
  unfold R.v6, N.v6.
  rewrite ?node_24318.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24320 (s : N.State) (i : N.Inputs) :
  R.v24320 (state s) (inputs i) = Zmod.unsigned (N.v24320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24320 s i)) at 1.
  unfold R.v24320, N.v24320.
  rewrite ?node_8995.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24321 (s : N.State) (i : N.Inputs) :
  R.v24321 (state s) (inputs i) = Zmod.unsigned (N.v24321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24321 s i)) at 1.
  unfold R.v24321, N.v24321.
  unfold R.v6, N.v6.
  rewrite ?node_9138.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24322 (s : N.State) (i : N.Inputs) :
  R.v24322 (state s) (inputs i) = Zmod.unsigned (N.v24322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24322 s i)) at 1.
  unfold R.v24322, N.v24322.
  rewrite ?node_24320.
  rewrite ?node_24321.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24323 (s : N.State) (i : N.Inputs) :
  R.v24323 (state s) (inputs i) = Zmod.unsigned (N.v24323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24323 s i)) at 1.
  unfold R.v24323, N.v24323.
  rewrite ?node_24319.
  rewrite ?node_24322.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24324 (s : N.State) (i : N.Inputs) :
  R.v24324 (state s) (inputs i) = Zmod.unsigned (N.v24324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24324 s i)) at 1.
  unfold R.v24324, N.v24324.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24325 (s : N.State) (i : N.Inputs) :
  R.v24325 (state s) (inputs i) = Zmod.unsigned (N.v24325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24325 s i)) at 1.
  unfold R.v24325, N.v24325.
  rewrite ?node_8999.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24326 (s : N.State) (i : N.Inputs) :
  R.v24326 (state s) (inputs i) = Zmod.unsigned (N.v24326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24326 s i)) at 1.
  unfold R.v24326, N.v24326.
  unfold R.v6, N.v6.
  rewrite !state_r862_nr_5F862.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r862_nr_5F862 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24327 (s : N.State) (i : N.Inputs) :
  R.v24327 (state s) (inputs i) = Zmod.unsigned (N.v24327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24327 s i)) at 1.
  unfold R.v24327, N.v24327.
  unfold R.v6, N.v6.
  rewrite ?node_8995.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24328 (s : N.State) (i : N.Inputs) :
  R.v24328 (state s) (inputs i) = Zmod.unsigned (N.v24328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24328 s i)) at 1.
  unfold R.v24328, N.v24328.
  rewrite ?node_24326.
  rewrite ?node_24327.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24329 (s : N.State) (i : N.Inputs) :
  R.v24329 (state s) (inputs i) = Zmod.unsigned (N.v24329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24329 s i)) at 1.
  unfold R.v24329, N.v24329.
  unfold R.v16484, N.v16484.
  rewrite ?node_24328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24330 (s : N.State) (i : N.Inputs) :
  R.v24330 (state s) (inputs i) = Zmod.unsigned (N.v24330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24330 s i)) at 1.
  unfold R.v24330, N.v24330.
  rewrite ?node_24325.
  rewrite ?node_24329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24331 (s : N.State) (i : N.Inputs) :
  R.v24331 (state s) (inputs i) = Zmod.unsigned (N.v24331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24331 s i)) at 1.
  unfold R.v24331, N.v24331.
  unfold R.v6, N.v6.
  rewrite ?node_24330.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24332 (s : N.State) (i : N.Inputs) :
  R.v24332 (state s) (inputs i) = Zmod.unsigned (N.v24332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24332 s i)) at 1.
  unfold R.v24332, N.v24332.
  rewrite ?node_9000.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24333 (s : N.State) (i : N.Inputs) :
  R.v24333 (state s) (inputs i) = Zmod.unsigned (N.v24333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24333 s i)) at 1.
  unfold R.v24333, N.v24333.
  unfold R.v6, N.v6.
  rewrite ?node_9181.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24334 (s : N.State) (i : N.Inputs) :
  R.v24334 (state s) (inputs i) = Zmod.unsigned (N.v24334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24334 s i)) at 1.
  unfold R.v24334, N.v24334.
  rewrite ?node_24332.
  rewrite ?node_24333.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24335 (s : N.State) (i : N.Inputs) :
  R.v24335 (state s) (inputs i) = Zmod.unsigned (N.v24335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24335 s i)) at 1.
  unfold R.v24335, N.v24335.
  rewrite ?node_24331.
  rewrite ?node_24334.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24336 (s : N.State) (i : N.Inputs) :
  R.v24336 (state s) (inputs i) = Zmod.unsigned (N.v24336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24336 s i)) at 1.
  unfold R.v24336, N.v24336.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24337 (s : N.State) (i : N.Inputs) :
  R.v24337 (state s) (inputs i) = Zmod.unsigned (N.v24337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24337 s i)) at 1.
  unfold R.v24337, N.v24337.
  rewrite ?node_9007.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24338 (s : N.State) (i : N.Inputs) :
  R.v24338 (state s) (inputs i) = Zmod.unsigned (N.v24338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24338 s i)) at 1.
  unfold R.v24338, N.v24338.
  unfold R.v16463, N.v16463.
  rewrite !state_r866_nr_5F866.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r866_nr_5F866 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24339 (s : N.State) (i : N.Inputs) :
  R.v24339 (state s) (inputs i) = Zmod.unsigned (N.v24339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24339 s i)) at 1.
  unfold R.v24339, N.v24339.
  unfold R.v16463, N.v16463.
  rewrite !state_r865_nr_5F865.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r865_nr_5F865 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24340 (s : N.State) (i : N.Inputs) :
  R.v24340 (state s) (inputs i) = Zmod.unsigned (N.v24340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24340 s i)) at 1.
  unfold R.v24340, N.v24340.
  unfold R.v6, N.v6.
  rewrite !state_r864_nr_5F864.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r864_nr_5F864 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24341 (s : N.State) (i : N.Inputs) :
  R.v24341 (state s) (inputs i) = Zmod.unsigned (N.v24341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24341 s i)) at 1.
  unfold R.v24341, N.v24341.
  unfold R.v6, N.v6.
  rewrite !state_r863_nr_5F863.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r863_nr_5F863 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24342 (s : N.State) (i : N.Inputs) :
  R.v24342 (state s) (inputs i) = Zmod.unsigned (N.v24342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24342 s i)) at 1.
  unfold R.v24342, N.v24342.
  rewrite ?node_24340.
  rewrite ?node_24341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24343 (s : N.State) (i : N.Inputs) :
  R.v24343 (state s) (inputs i) = Zmod.unsigned (N.v24343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24343 s i)) at 1.
  unfold R.v24343, N.v24343.
  unfold R.v16484, N.v16484.
  rewrite ?node_24342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24344 (s : N.State) (i : N.Inputs) :
  R.v24344 (state s) (inputs i) = Zmod.unsigned (N.v24344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24344 s i)) at 1.
  unfold R.v24344, N.v24344.
  rewrite ?node_24337.
  rewrite ?node_24338.
  rewrite ?node_24339.
  rewrite ?node_24343.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24345 (s : N.State) (i : N.Inputs) :
  R.v24345 (state s) (inputs i) = Zmod.unsigned (N.v24345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24345 s i)) at 1.
  unfold R.v24345, N.v24345.
  unfold R.v6, N.v6.
  rewrite ?node_24344.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24346 (s : N.State) (i : N.Inputs) :
  R.v24346 (state s) (inputs i) = Zmod.unsigned (N.v24346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24346 s i)) at 1.
  unfold R.v24346, N.v24346.
  rewrite ?node_9008.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24347 (s : N.State) (i : N.Inputs) :
  R.v24347 (state s) (inputs i) = Zmod.unsigned (N.v24347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24347 s i)) at 1.
  unfold R.v24347, N.v24347.
  unfold R.v6, N.v6.
  rewrite ?node_9146.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24348 (s : N.State) (i : N.Inputs) :
  R.v24348 (state s) (inputs i) = Zmod.unsigned (N.v24348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24348 s i)) at 1.
  unfold R.v24348, N.v24348.
  unfold R.v6, N.v6.
  rewrite ?node_9185.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24349 (s : N.State) (i : N.Inputs) :
  R.v24349 (state s) (inputs i) = Zmod.unsigned (N.v24349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24349 s i)) at 1.
  unfold R.v24349, N.v24349.
  rewrite ?node_24346.
  rewrite ?node_24347.
  rewrite ?node_24348.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24350 (s : N.State) (i : N.Inputs) :
  R.v24350 (state s) (inputs i) = Zmod.unsigned (N.v24350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24350 s i)) at 1.
  unfold R.v24350, N.v24350.
  rewrite ?node_24345.
  rewrite ?node_24349.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24351 (s : N.State) (i : N.Inputs) :
  R.v24351 (state s) (inputs i) = Zmod.unsigned (N.v24351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24351 s i)) at 1.
  unfold R.v24351, N.v24351.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24352 (s : N.State) (i : N.Inputs) :
  R.v24352 (state s) (inputs i) = Zmod.unsigned (N.v24352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24352 s i)) at 1.
  unfold R.v24352, N.v24352.
  unfold R.v16463, N.v16463.
  rewrite !state_r865_nr_5F865.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r865_nr_5F865 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24353 (s : N.State) (i : N.Inputs) :
  R.v24353 (state s) (inputs i) = Zmod.unsigned (N.v24353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24353 s i)) at 1.
  unfold R.v24353, N.v24353.
  unfold R.v6, N.v6.
  rewrite !state_r864_nr_5F864.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r864_nr_5F864 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24354 (s : N.State) (i : N.Inputs) :
  R.v24354 (state s) (inputs i) = Zmod.unsigned (N.v24354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24354 s i)) at 1.
  unfold R.v24354, N.v24354.
  unfold R.v6, N.v6.
  rewrite !state_r863_nr_5F863.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r863_nr_5F863 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24355 (s : N.State) (i : N.Inputs) :
  R.v24355 (state s) (inputs i) = Zmod.unsigned (N.v24355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24355 s i)) at 1.
  unfold R.v24355, N.v24355.
  rewrite ?node_24353.
  rewrite ?node_24354.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24356 (s : N.State) (i : N.Inputs) :
  R.v24356 (state s) (inputs i) = Zmod.unsigned (N.v24356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24356 s i)) at 1.
  unfold R.v24356, N.v24356.
  unfold R.v16484, N.v16484.
  rewrite ?node_24355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24357 (s : N.State) (i : N.Inputs) :
  R.v24357 (state s) (inputs i) = Zmod.unsigned (N.v24357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24357 s i)) at 1.
  unfold R.v24357, N.v24357.
  rewrite ?node_24352.
  rewrite ?node_24356.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24358 (s : N.State) (i : N.Inputs) :
  R.v24358 (state s) (inputs i) = Zmod.unsigned (N.v24358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24358 s i)) at 1.
  unfold R.v24358, N.v24358.
  unfold R.v6, N.v6.
  rewrite ?node_24357.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24359 (s : N.State) (i : N.Inputs) :
  R.v24359 (state s) (inputs i) = Zmod.unsigned (N.v24359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24359 s i)) at 1.
  unfold R.v24359, N.v24359.
  rewrite ?node_9003.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24360 (s : N.State) (i : N.Inputs) :
  R.v24360 (state s) (inputs i) = Zmod.unsigned (N.v24360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24360 s i)) at 1.
  unfold R.v24360, N.v24360.
  unfold R.v6, N.v6.
  rewrite ?node_9146.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24361 (s : N.State) (i : N.Inputs) :
  R.v24361 (state s) (inputs i) = Zmod.unsigned (N.v24361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24361 s i)) at 1.
  unfold R.v24361, N.v24361.
  rewrite ?node_24359.
  rewrite ?node_24360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24362 (s : N.State) (i : N.Inputs) :
  R.v24362 (state s) (inputs i) = Zmod.unsigned (N.v24362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24362 s i)) at 1.
  unfold R.v24362, N.v24362.
  rewrite ?node_24358.
  rewrite ?node_24361.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24363 (s : N.State) (i : N.Inputs) :
  R.v24363 (state s) (inputs i) = Zmod.unsigned (N.v24363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24363 s i)) at 1.
  unfold R.v24363, N.v24363.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24364 (s : N.State) (i : N.Inputs) :
  R.v24364 (state s) (inputs i) = Zmod.unsigned (N.v24364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24364 s i)) at 1.
  unfold R.v24364, N.v24364.
  rewrite ?node_9007.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24365 (s : N.State) (i : N.Inputs) :
  R.v24365 (state s) (inputs i) = Zmod.unsigned (N.v24365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24365 s i)) at 1.
  unfold R.v24365, N.v24365.
  unfold R.v6, N.v6.
  rewrite !state_r866_nr_5F866.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r866_nr_5F866 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24366 (s : N.State) (i : N.Inputs) :
  R.v24366 (state s) (inputs i) = Zmod.unsigned (N.v24366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24366 s i)) at 1.
  unfold R.v24366, N.v24366.
  unfold R.v6, N.v6.
  rewrite ?node_9003.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24367 (s : N.State) (i : N.Inputs) :
  R.v24367 (state s) (inputs i) = Zmod.unsigned (N.v24367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24367 s i)) at 1.
  unfold R.v24367, N.v24367.
  rewrite ?node_24365.
  rewrite ?node_24366.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24368 (s : N.State) (i : N.Inputs) :
  R.v24368 (state s) (inputs i) = Zmod.unsigned (N.v24368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24368 s i)) at 1.
  unfold R.v24368, N.v24368.
  unfold R.v16484, N.v16484.
  rewrite ?node_24367.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24369 (s : N.State) (i : N.Inputs) :
  R.v24369 (state s) (inputs i) = Zmod.unsigned (N.v24369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24369 s i)) at 1.
  unfold R.v24369, N.v24369.
  rewrite ?node_24364.
  rewrite ?node_24368.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24370 (s : N.State) (i : N.Inputs) :
  R.v24370 (state s) (inputs i) = Zmod.unsigned (N.v24370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24370 s i)) at 1.
  unfold R.v24370, N.v24370.
  unfold R.v6, N.v6.
  rewrite ?node_24369.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24371 (s : N.State) (i : N.Inputs) :
  R.v24371 (state s) (inputs i) = Zmod.unsigned (N.v24371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24371 s i)) at 1.
  unfold R.v24371, N.v24371.
  rewrite ?node_9008.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24372 (s : N.State) (i : N.Inputs) :
  R.v24372 (state s) (inputs i) = Zmod.unsigned (N.v24372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24372 s i)) at 1.
  unfold R.v24372, N.v24372.
  unfold R.v6, N.v6.
  rewrite ?node_9185.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24373 (s : N.State) (i : N.Inputs) :
  R.v24373 (state s) (inputs i) = Zmod.unsigned (N.v24373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24373 s i)) at 1.
  unfold R.v24373, N.v24373.
  rewrite ?node_24371.
  rewrite ?node_24372.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24374 (s : N.State) (i : N.Inputs) :
  R.v24374 (state s) (inputs i) = Zmod.unsigned (N.v24374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24374 s i)) at 1.
  unfold R.v24374, N.v24374.
  rewrite ?node_24370.
  rewrite ?node_24373.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24375 (s : N.State) (i : N.Inputs) :
  R.v24375 (state s) (inputs i) = Zmod.unsigned (N.v24375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24375 s i)) at 1.
  unfold R.v24375, N.v24375.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24376 (s : N.State) (i : N.Inputs) :
  R.v24376 (state s) (inputs i) = Zmod.unsigned (N.v24376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24376 s i)) at 1.
  unfold R.v24376, N.v24376.
  rewrite ?node_9096.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24377 (s : N.State) (i : N.Inputs) :
  R.v24377 (state s) (inputs i) = Zmod.unsigned (N.v24377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24377 s i)) at 1.
  unfold R.v24377, N.v24377.
  unfold R.v16463, N.v16463.
  rewrite !state_r871_nr_5F871.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r871_nr_5F871 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24378 (s : N.State) (i : N.Inputs) :
  R.v24378 (state s) (inputs i) = Zmod.unsigned (N.v24378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24378 s i)) at 1.
  unfold R.v24378, N.v24378.
  unfold R.v16463, N.v16463.
  rewrite !state_r870_nr_5F870.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r870_nr_5F870 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24379 (s : N.State) (i : N.Inputs) :
  R.v24379 (state s) (inputs i) = Zmod.unsigned (N.v24379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24379 s i)) at 1.
  unfold R.v24379, N.v24379.
  unfold R.v6, N.v6.
  rewrite !state_r869_nr_5F869.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r869_nr_5F869 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24380 (s : N.State) (i : N.Inputs) :
  R.v24380 (state s) (inputs i) = Zmod.unsigned (N.v24380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24380 s i)) at 1.
  unfold R.v24380, N.v24380.
  unfold R.v6, N.v6.
  rewrite !state_r868_nr_5F868.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r868_nr_5F868 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24381 (s : N.State) (i : N.Inputs) :
  R.v24381 (state s) (inputs i) = Zmod.unsigned (N.v24381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24381 s i)) at 1.
  unfold R.v24381, N.v24381.
  rewrite ?node_24379.
  rewrite ?node_24380.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24382 (s : N.State) (i : N.Inputs) :
  R.v24382 (state s) (inputs i) = Zmod.unsigned (N.v24382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24382 s i)) at 1.
  unfold R.v24382, N.v24382.
  unfold R.v16484, N.v16484.
  rewrite ?node_24381.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24383 (s : N.State) (i : N.Inputs) :
  R.v24383 (state s) (inputs i) = Zmod.unsigned (N.v24383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24383 s i)) at 1.
  unfold R.v24383, N.v24383.
  rewrite ?node_24376.
  rewrite ?node_24377.
  rewrite ?node_24378.
  rewrite ?node_24382.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24384 (s : N.State) (i : N.Inputs) :
  R.v24384 (state s) (inputs i) = Zmod.unsigned (N.v24384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24384 s i)) at 1.
  unfold R.v24384, N.v24384.
  unfold R.v6, N.v6.
  rewrite ?node_24383.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24385 (s : N.State) (i : N.Inputs) :
  R.v24385 (state s) (inputs i) = Zmod.unsigned (N.v24385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24385 s i)) at 1.
  unfold R.v24385, N.v24385.
  rewrite ?node_9097.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24386 (s : N.State) (i : N.Inputs) :
  R.v24386 (state s) (inputs i) = Zmod.unsigned (N.v24386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24386 s i)) at 1.
  unfold R.v24386, N.v24386.
  unfold R.v6, N.v6.
  rewrite ?node_9236.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24387 (s : N.State) (i : N.Inputs) :
  R.v24387 (state s) (inputs i) = Zmod.unsigned (N.v24387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24387 s i)) at 1.
  unfold R.v24387, N.v24387.
  unfold R.v6, N.v6.
  rewrite ?node_9298.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24388 (s : N.State) (i : N.Inputs) :
  R.v24388 (state s) (inputs i) = Zmod.unsigned (N.v24388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24388 s i)) at 1.
  unfold R.v24388, N.v24388.
  rewrite ?node_24385.
  rewrite ?node_24386.
  rewrite ?node_24387.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24389 (s : N.State) (i : N.Inputs) :
  R.v24389 (state s) (inputs i) = Zmod.unsigned (N.v24389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24389 s i)) at 1.
  unfold R.v24389, N.v24389.
  rewrite ?node_24384.
  rewrite ?node_24388.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24390 (s : N.State) (i : N.Inputs) :
  R.v24390 (state s) (inputs i) = Zmod.unsigned (N.v24390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24390 s i)) at 1.
  unfold R.v24390, N.v24390.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24391 (s : N.State) (i : N.Inputs) :
  R.v24391 (state s) (inputs i) = Zmod.unsigned (N.v24391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24391 s i)) at 1.
  unfold R.v24391, N.v24391.
  unfold R.v16463, N.v16463.
  rewrite !state_r870_nr_5F870.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r870_nr_5F870 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24392 (s : N.State) (i : N.Inputs) :
  R.v24392 (state s) (inputs i) = Zmod.unsigned (N.v24392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24392 s i)) at 1.
  unfold R.v24392, N.v24392.
  unfold R.v6, N.v6.
  rewrite !state_r869_nr_5F869.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r869_nr_5F869 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24393 (s : N.State) (i : N.Inputs) :
  R.v24393 (state s) (inputs i) = Zmod.unsigned (N.v24393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24393 s i)) at 1.
  unfold R.v24393, N.v24393.
  unfold R.v6, N.v6.
  rewrite !state_r868_nr_5F868.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r868_nr_5F868 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24394 (s : N.State) (i : N.Inputs) :
  R.v24394 (state s) (inputs i) = Zmod.unsigned (N.v24394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24394 s i)) at 1.
  unfold R.v24394, N.v24394.
  rewrite ?node_24392.
  rewrite ?node_24393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24395 (s : N.State) (i : N.Inputs) :
  R.v24395 (state s) (inputs i) = Zmod.unsigned (N.v24395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24395 s i)) at 1.
  unfold R.v24395, N.v24395.
  unfold R.v16484, N.v16484.
  rewrite ?node_24394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24396 (s : N.State) (i : N.Inputs) :
  R.v24396 (state s) (inputs i) = Zmod.unsigned (N.v24396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24396 s i)) at 1.
  unfold R.v24396, N.v24396.
  rewrite ?node_24391.
  rewrite ?node_24395.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24397 (s : N.State) (i : N.Inputs) :
  R.v24397 (state s) (inputs i) = Zmod.unsigned (N.v24397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24397 s i)) at 1.
  unfold R.v24397, N.v24397.
  unfold R.v6, N.v6.
  rewrite ?node_24396.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24398 (s : N.State) (i : N.Inputs) :
  R.v24398 (state s) (inputs i) = Zmod.unsigned (N.v24398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24398 s i)) at 1.
  unfold R.v24398, N.v24398.
  rewrite ?node_9092.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24399 (s : N.State) (i : N.Inputs) :
  R.v24399 (state s) (inputs i) = Zmod.unsigned (N.v24399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24399 s i)) at 1.
  unfold R.v24399, N.v24399.
  unfold R.v6, N.v6.
  rewrite ?node_9236.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24400 (s : N.State) (i : N.Inputs) :
  R.v24400 (state s) (inputs i) = Zmod.unsigned (N.v24400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24400 s i)) at 1.
  unfold R.v24400, N.v24400.
  rewrite ?node_24398.
  rewrite ?node_24399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24401 (s : N.State) (i : N.Inputs) :
  R.v24401 (state s) (inputs i) = Zmod.unsigned (N.v24401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24401 s i)) at 1.
  unfold R.v24401, N.v24401.
  rewrite ?node_24397.
  rewrite ?node_24400.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24402 (s : N.State) (i : N.Inputs) :
  R.v24402 (state s) (inputs i) = Zmod.unsigned (N.v24402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24402 s i)) at 1.
  unfold R.v24402, N.v24402.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24403 (s : N.State) (i : N.Inputs) :
  R.v24403 (state s) (inputs i) = Zmod.unsigned (N.v24403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24403 s i)) at 1.
  unfold R.v24403, N.v24403.
  rewrite ?node_9096.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24404 (s : N.State) (i : N.Inputs) :
  R.v24404 (state s) (inputs i) = Zmod.unsigned (N.v24404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24404 s i)) at 1.
  unfold R.v24404, N.v24404.
  unfold R.v6, N.v6.
  rewrite !state_r871_nr_5F871.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r871_nr_5F871 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24405 (s : N.State) (i : N.Inputs) :
  R.v24405 (state s) (inputs i) = Zmod.unsigned (N.v24405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24405 s i)) at 1.
  unfold R.v24405, N.v24405.
  unfold R.v6, N.v6.
  rewrite ?node_9092.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24406 (s : N.State) (i : N.Inputs) :
  R.v24406 (state s) (inputs i) = Zmod.unsigned (N.v24406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24406 s i)) at 1.
  unfold R.v24406, N.v24406.
  rewrite ?node_24404.
  rewrite ?node_24405.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24407 (s : N.State) (i : N.Inputs) :
  R.v24407 (state s) (inputs i) = Zmod.unsigned (N.v24407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24407 s i)) at 1.
  unfold R.v24407, N.v24407.
  unfold R.v16484, N.v16484.
  rewrite ?node_24406.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24408 (s : N.State) (i : N.Inputs) :
  R.v24408 (state s) (inputs i) = Zmod.unsigned (N.v24408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24408 s i)) at 1.
  unfold R.v24408, N.v24408.
  rewrite ?node_24403.
  rewrite ?node_24407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24409 (s : N.State) (i : N.Inputs) :
  R.v24409 (state s) (inputs i) = Zmod.unsigned (N.v24409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24409 s i)) at 1.
  unfold R.v24409, N.v24409.
  unfold R.v6, N.v6.
  rewrite ?node_24408.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24410 (s : N.State) (i : N.Inputs) :
  R.v24410 (state s) (inputs i) = Zmod.unsigned (N.v24410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24410 s i)) at 1.
  unfold R.v24410, N.v24410.
  rewrite ?node_9097.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24411 (s : N.State) (i : N.Inputs) :
  R.v24411 (state s) (inputs i) = Zmod.unsigned (N.v24411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24411 s i)) at 1.
  unfold R.v24411, N.v24411.
  unfold R.v6, N.v6.
  rewrite ?node_9298.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24412 (s : N.State) (i : N.Inputs) :
  R.v24412 (state s) (inputs i) = Zmod.unsigned (N.v24412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24412 s i)) at 1.
  unfold R.v24412, N.v24412.
  rewrite ?node_24410.
  rewrite ?node_24411.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24413 (s : N.State) (i : N.Inputs) :
  R.v24413 (state s) (inputs i) = Zmod.unsigned (N.v24413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24413 s i)) at 1.
  unfold R.v24413, N.v24413.
  rewrite ?node_24409.
  rewrite ?node_24412.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24414 (s : N.State) (i : N.Inputs) :
  R.v24414 (state s) (inputs i) = Zmod.unsigned (N.v24414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24414 s i)) at 1.
  unfold R.v24414, N.v24414.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24415 (s : N.State) (i : N.Inputs) :
  R.v24415 (state s) (inputs i) = Zmod.unsigned (N.v24415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24415 s i)) at 1.
  unfold R.v24415, N.v24415.
  rewrite ?node_9103.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24416 (s : N.State) (i : N.Inputs) :
  R.v24416 (state s) (inputs i) = Zmod.unsigned (N.v24416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24416 s i)) at 1.
  unfold R.v24416, N.v24416.
  unfold R.v16463, N.v16463.
  rewrite !state_r875_nr_5F875.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r875_nr_5F875 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24417 (s : N.State) (i : N.Inputs) :
  R.v24417 (state s) (inputs i) = Zmod.unsigned (N.v24417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24417 s i)) at 1.
  unfold R.v24417, N.v24417.
  unfold R.v16463, N.v16463.
  rewrite !state_r874_nr_5F874.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r874_nr_5F874 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24418 (s : N.State) (i : N.Inputs) :
  R.v24418 (state s) (inputs i) = Zmod.unsigned (N.v24418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24418 s i)) at 1.
  unfold R.v24418, N.v24418.
  unfold R.v6, N.v6.
  rewrite !state_r873_nr_5F873.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r873_nr_5F873 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24419 (s : N.State) (i : N.Inputs) :
  R.v24419 (state s) (inputs i) = Zmod.unsigned (N.v24419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24419 s i)) at 1.
  unfold R.v24419, N.v24419.
  unfold R.v6, N.v6.
  rewrite !state_r872_nr_5F872.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r872_nr_5F872 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24420 (s : N.State) (i : N.Inputs) :
  R.v24420 (state s) (inputs i) = Zmod.unsigned (N.v24420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24420 s i)) at 1.
  unfold R.v24420, N.v24420.
  rewrite ?node_24418.
  rewrite ?node_24419.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24421 (s : N.State) (i : N.Inputs) :
  R.v24421 (state s) (inputs i) = Zmod.unsigned (N.v24421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24421 s i)) at 1.
  unfold R.v24421, N.v24421.
  unfold R.v16484, N.v16484.
  rewrite ?node_24420.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24422 (s : N.State) (i : N.Inputs) :
  R.v24422 (state s) (inputs i) = Zmod.unsigned (N.v24422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24422 s i)) at 1.
  unfold R.v24422, N.v24422.
  rewrite ?node_24415.
  rewrite ?node_24416.
  rewrite ?node_24417.
  rewrite ?node_24421.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24423 (s : N.State) (i : N.Inputs) :
  R.v24423 (state s) (inputs i) = Zmod.unsigned (N.v24423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24423 s i)) at 1.
  unfold R.v24423, N.v24423.
  unfold R.v6, N.v6.
  rewrite ?node_24422.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24424 (s : N.State) (i : N.Inputs) :
  R.v24424 (state s) (inputs i) = Zmod.unsigned (N.v24424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24424 s i)) at 1.
  unfold R.v24424, N.v24424.
  rewrite ?node_9104.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24425 (s : N.State) (i : N.Inputs) :
  R.v24425 (state s) (inputs i) = Zmod.unsigned (N.v24425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24425 s i)) at 1.
  unfold R.v24425, N.v24425.
  unfold R.v6, N.v6.
  rewrite ?node_9243.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24426 (s : N.State) (i : N.Inputs) :
  R.v24426 (state s) (inputs i) = Zmod.unsigned (N.v24426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24426 s i)) at 1.
  unfold R.v24426, N.v24426.
  unfold R.v6, N.v6.
  rewrite ?node_9301.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24427 (s : N.State) (i : N.Inputs) :
  R.v24427 (state s) (inputs i) = Zmod.unsigned (N.v24427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24427 s i)) at 1.
  unfold R.v24427, N.v24427.
  rewrite ?node_24424.
  rewrite ?node_24425.
  rewrite ?node_24426.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24428 (s : N.State) (i : N.Inputs) :
  R.v24428 (state s) (inputs i) = Zmod.unsigned (N.v24428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24428 s i)) at 1.
  unfold R.v24428, N.v24428.
  rewrite ?node_24423.
  rewrite ?node_24427.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24429 (s : N.State) (i : N.Inputs) :
  R.v24429 (state s) (inputs i) = Zmod.unsigned (N.v24429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24429 s i)) at 1.
  unfold R.v24429, N.v24429.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24430 (s : N.State) (i : N.Inputs) :
  R.v24430 (state s) (inputs i) = Zmod.unsigned (N.v24430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24430 s i)) at 1.
  unfold R.v24430, N.v24430.
  unfold R.v16463, N.v16463.
  rewrite !state_r874_nr_5F874.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r874_nr_5F874 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24431 (s : N.State) (i : N.Inputs) :
  R.v24431 (state s) (inputs i) = Zmod.unsigned (N.v24431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24431 s i)) at 1.
  unfold R.v24431, N.v24431.
  unfold R.v6, N.v6.
  rewrite !state_r873_nr_5F873.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r873_nr_5F873 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24432 (s : N.State) (i : N.Inputs) :
  R.v24432 (state s) (inputs i) = Zmod.unsigned (N.v24432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24432 s i)) at 1.
  unfold R.v24432, N.v24432.
  unfold R.v6, N.v6.
  rewrite !state_r872_nr_5F872.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r872_nr_5F872 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24433 (s : N.State) (i : N.Inputs) :
  R.v24433 (state s) (inputs i) = Zmod.unsigned (N.v24433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24433 s i)) at 1.
  unfold R.v24433, N.v24433.
  rewrite ?node_24431.
  rewrite ?node_24432.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24434 (s : N.State) (i : N.Inputs) :
  R.v24434 (state s) (inputs i) = Zmod.unsigned (N.v24434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24434 s i)) at 1.
  unfold R.v24434, N.v24434.
  unfold R.v16484, N.v16484.
  rewrite ?node_24433.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24435 (s : N.State) (i : N.Inputs) :
  R.v24435 (state s) (inputs i) = Zmod.unsigned (N.v24435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24435 s i)) at 1.
  unfold R.v24435, N.v24435.
  rewrite ?node_24430.
  rewrite ?node_24434.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24436 (s : N.State) (i : N.Inputs) :
  R.v24436 (state s) (inputs i) = Zmod.unsigned (N.v24436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24436 s i)) at 1.
  unfold R.v24436, N.v24436.
  unfold R.v6, N.v6.
  rewrite ?node_24435.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24437 (s : N.State) (i : N.Inputs) :
  R.v24437 (state s) (inputs i) = Zmod.unsigned (N.v24437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24437 s i)) at 1.
  unfold R.v24437, N.v24437.
  rewrite ?node_9099.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24438 (s : N.State) (i : N.Inputs) :
  R.v24438 (state s) (inputs i) = Zmod.unsigned (N.v24438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24438 s i)) at 1.
  unfold R.v24438, N.v24438.
  unfold R.v6, N.v6.
  rewrite ?node_9243.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24439 (s : N.State) (i : N.Inputs) :
  R.v24439 (state s) (inputs i) = Zmod.unsigned (N.v24439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24439 s i)) at 1.
  unfold R.v24439, N.v24439.
  rewrite ?node_24437.
  rewrite ?node_24438.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24440 (s : N.State) (i : N.Inputs) :
  R.v24440 (state s) (inputs i) = Zmod.unsigned (N.v24440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24440 s i)) at 1.
  unfold R.v24440, N.v24440.
  rewrite ?node_24436.
  rewrite ?node_24439.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24441 (s : N.State) (i : N.Inputs) :
  R.v24441 (state s) (inputs i) = Zmod.unsigned (N.v24441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24441 s i)) at 1.
  unfold R.v24441, N.v24441.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24442 (s : N.State) (i : N.Inputs) :
  R.v24442 (state s) (inputs i) = Zmod.unsigned (N.v24442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24442 s i)) at 1.
  unfold R.v24442, N.v24442.
  rewrite ?node_9103.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24443 (s : N.State) (i : N.Inputs) :
  R.v24443 (state s) (inputs i) = Zmod.unsigned (N.v24443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24443 s i)) at 1.
  unfold R.v24443, N.v24443.
  unfold R.v6, N.v6.
  rewrite !state_r875_nr_5F875.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r875_nr_5F875 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24444 (s : N.State) (i : N.Inputs) :
  R.v24444 (state s) (inputs i) = Zmod.unsigned (N.v24444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24444 s i)) at 1.
  unfold R.v24444, N.v24444.
  unfold R.v6, N.v6.
  rewrite ?node_9099.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24445 (s : N.State) (i : N.Inputs) :
  R.v24445 (state s) (inputs i) = Zmod.unsigned (N.v24445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24445 s i)) at 1.
  unfold R.v24445, N.v24445.
  rewrite ?node_24443.
  rewrite ?node_24444.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24446 (s : N.State) (i : N.Inputs) :
  R.v24446 (state s) (inputs i) = Zmod.unsigned (N.v24446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24446 s i)) at 1.
  unfold R.v24446, N.v24446.
  unfold R.v16484, N.v16484.
  rewrite ?node_24445.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24447 (s : N.State) (i : N.Inputs) :
  R.v24447 (state s) (inputs i) = Zmod.unsigned (N.v24447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24447 s i)) at 1.
  unfold R.v24447, N.v24447.
  rewrite ?node_24442.
  rewrite ?node_24446.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24448 (s : N.State) (i : N.Inputs) :
  R.v24448 (state s) (inputs i) = Zmod.unsigned (N.v24448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24448 s i)) at 1.
  unfold R.v24448, N.v24448.
  unfold R.v6, N.v6.
  rewrite ?node_24447.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24449 (s : N.State) (i : N.Inputs) :
  R.v24449 (state s) (inputs i) = Zmod.unsigned (N.v24449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24449 s i)) at 1.
  unfold R.v24449, N.v24449.
  rewrite ?node_9104.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24450 (s : N.State) (i : N.Inputs) :
  R.v24450 (state s) (inputs i) = Zmod.unsigned (N.v24450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24450 s i)) at 1.
  unfold R.v24450, N.v24450.
  unfold R.v6, N.v6.
  rewrite ?node_9301.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24451 (s : N.State) (i : N.Inputs) :
  R.v24451 (state s) (inputs i) = Zmod.unsigned (N.v24451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24451 s i)) at 1.
  unfold R.v24451, N.v24451.
  rewrite ?node_24449.
  rewrite ?node_24450.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24452 (s : N.State) (i : N.Inputs) :
  R.v24452 (state s) (inputs i) = Zmod.unsigned (N.v24452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24452 s i)) at 1.
  unfold R.v24452, N.v24452.
  rewrite ?node_24448.
  rewrite ?node_24451.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24453 (s : N.State) (i : N.Inputs) :
  R.v24453 (state s) (inputs i) = Zmod.unsigned (N.v24453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24453 s i)) at 1.
  unfold R.v24453, N.v24453.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24454 (s : N.State) (i : N.Inputs) :
  R.v24454 (state s) (inputs i) = Zmod.unsigned (N.v24454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24454 s i)) at 1.
  unfold R.v24454, N.v24454.
  rewrite ?node_9111.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24455 (s : N.State) (i : N.Inputs) :
  R.v24455 (state s) (inputs i) = Zmod.unsigned (N.v24455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24455 s i)) at 1.
  unfold R.v24455, N.v24455.
  unfold R.v16463, N.v16463.
  rewrite !state_r879_nr_5F879.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r879_nr_5F879 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24456 (s : N.State) (i : N.Inputs) :
  R.v24456 (state s) (inputs i) = Zmod.unsigned (N.v24456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24456 s i)) at 1.
  unfold R.v24456, N.v24456.
  unfold R.v16463, N.v16463.
  rewrite !state_r878_nr_5F878.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r878_nr_5F878 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24457 (s : N.State) (i : N.Inputs) :
  R.v24457 (state s) (inputs i) = Zmod.unsigned (N.v24457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24457 s i)) at 1.
  unfold R.v24457, N.v24457.
  unfold R.v6, N.v6.
  rewrite !state_r877_nr_5F877.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r877_nr_5F877 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24458 (s : N.State) (i : N.Inputs) :
  R.v24458 (state s) (inputs i) = Zmod.unsigned (N.v24458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24458 s i)) at 1.
  unfold R.v24458, N.v24458.
  unfold R.v6, N.v6.
  rewrite !state_r876_nr_5F876.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r876_nr_5F876 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24459 (s : N.State) (i : N.Inputs) :
  R.v24459 (state s) (inputs i) = Zmod.unsigned (N.v24459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24459 s i)) at 1.
  unfold R.v24459, N.v24459.
  rewrite ?node_24457.
  rewrite ?node_24458.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24460 (s : N.State) (i : N.Inputs) :
  R.v24460 (state s) (inputs i) = Zmod.unsigned (N.v24460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24460 s i)) at 1.
  unfold R.v24460, N.v24460.
  unfold R.v16484, N.v16484.
  rewrite ?node_24459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24461 (s : N.State) (i : N.Inputs) :
  R.v24461 (state s) (inputs i) = Zmod.unsigned (N.v24461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24461 s i)) at 1.
  unfold R.v24461, N.v24461.
  rewrite ?node_24454.
  rewrite ?node_24455.
  rewrite ?node_24456.
  rewrite ?node_24460.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24462 (s : N.State) (i : N.Inputs) :
  R.v24462 (state s) (inputs i) = Zmod.unsigned (N.v24462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24462 s i)) at 1.
  unfold R.v24462, N.v24462.
  unfold R.v6, N.v6.
  rewrite ?node_24461.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24463 (s : N.State) (i : N.Inputs) :
  R.v24463 (state s) (inputs i) = Zmod.unsigned (N.v24463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24463 s i)) at 1.
  unfold R.v24463, N.v24463.
  rewrite ?node_9112.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24464 (s : N.State) (i : N.Inputs) :
  R.v24464 (state s) (inputs i) = Zmod.unsigned (N.v24464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24464 s i)) at 1.
  unfold R.v24464, N.v24464.
  unfold R.v6, N.v6.
  rewrite ?node_9251.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24465 (s : N.State) (i : N.Inputs) :
  R.v24465 (state s) (inputs i) = Zmod.unsigned (N.v24465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24465 s i)) at 1.
  unfold R.v24465, N.v24465.
  unfold R.v6, N.v6.
  rewrite ?node_9305.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24466 (s : N.State) (i : N.Inputs) :
  R.v24466 (state s) (inputs i) = Zmod.unsigned (N.v24466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24466 s i)) at 1.
  unfold R.v24466, N.v24466.
  rewrite ?node_24463.
  rewrite ?node_24464.
  rewrite ?node_24465.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24467 (s : N.State) (i : N.Inputs) :
  R.v24467 (state s) (inputs i) = Zmod.unsigned (N.v24467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24467 s i)) at 1.
  unfold R.v24467, N.v24467.
  rewrite ?node_24462.
  rewrite ?node_24466.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24468 (s : N.State) (i : N.Inputs) :
  R.v24468 (state s) (inputs i) = Zmod.unsigned (N.v24468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24468 s i)) at 1.
  unfold R.v24468, N.v24468.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24469 (s : N.State) (i : N.Inputs) :
  R.v24469 (state s) (inputs i) = Zmod.unsigned (N.v24469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24469 s i)) at 1.
  unfold R.v24469, N.v24469.
  unfold R.v16463, N.v16463.
  rewrite !state_r878_nr_5F878.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r878_nr_5F878 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24470 (s : N.State) (i : N.Inputs) :
  R.v24470 (state s) (inputs i) = Zmod.unsigned (N.v24470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24470 s i)) at 1.
  unfold R.v24470, N.v24470.
  unfold R.v6, N.v6.
  rewrite !state_r877_nr_5F877.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r877_nr_5F877 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24471 (s : N.State) (i : N.Inputs) :
  R.v24471 (state s) (inputs i) = Zmod.unsigned (N.v24471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24471 s i)) at 1.
  unfold R.v24471, N.v24471.
  unfold R.v6, N.v6.
  rewrite !state_r876_nr_5F876.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r876_nr_5F876 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24472 (s : N.State) (i : N.Inputs) :
  R.v24472 (state s) (inputs i) = Zmod.unsigned (N.v24472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24472 s i)) at 1.
  unfold R.v24472, N.v24472.
  rewrite ?node_24470.
  rewrite ?node_24471.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24473 (s : N.State) (i : N.Inputs) :
  R.v24473 (state s) (inputs i) = Zmod.unsigned (N.v24473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24473 s i)) at 1.
  unfold R.v24473, N.v24473.
  unfold R.v16484, N.v16484.
  rewrite ?node_24472.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24474 (s : N.State) (i : N.Inputs) :
  R.v24474 (state s) (inputs i) = Zmod.unsigned (N.v24474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24474 s i)) at 1.
  unfold R.v24474, N.v24474.
  rewrite ?node_24469.
  rewrite ?node_24473.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24475 (s : N.State) (i : N.Inputs) :
  R.v24475 (state s) (inputs i) = Zmod.unsigned (N.v24475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24475 s i)) at 1.
  unfold R.v24475, N.v24475.
  unfold R.v6, N.v6.
  rewrite ?node_24474.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24476 (s : N.State) (i : N.Inputs) :
  R.v24476 (state s) (inputs i) = Zmod.unsigned (N.v24476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24476 s i)) at 1.
  unfold R.v24476, N.v24476.
  rewrite ?node_9107.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24477 (s : N.State) (i : N.Inputs) :
  R.v24477 (state s) (inputs i) = Zmod.unsigned (N.v24477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24477 s i)) at 1.
  unfold R.v24477, N.v24477.
  unfold R.v6, N.v6.
  rewrite ?node_9251.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24478 (s : N.State) (i : N.Inputs) :
  R.v24478 (state s) (inputs i) = Zmod.unsigned (N.v24478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24478 s i)) at 1.
  unfold R.v24478, N.v24478.
  rewrite ?node_24476.
  rewrite ?node_24477.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24479 (s : N.State) (i : N.Inputs) :
  R.v24479 (state s) (inputs i) = Zmod.unsigned (N.v24479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24479 s i)) at 1.
  unfold R.v24479, N.v24479.
  rewrite ?node_24475.
  rewrite ?node_24478.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24480 (s : N.State) (i : N.Inputs) :
  R.v24480 (state s) (inputs i) = Zmod.unsigned (N.v24480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24480 s i)) at 1.
  unfold R.v24480, N.v24480.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24481 (s : N.State) (i : N.Inputs) :
  R.v24481 (state s) (inputs i) = Zmod.unsigned (N.v24481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24481 s i)) at 1.
  unfold R.v24481, N.v24481.
  rewrite ?node_9111.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24482 (s : N.State) (i : N.Inputs) :
  R.v24482 (state s) (inputs i) = Zmod.unsigned (N.v24482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24482 s i)) at 1.
  unfold R.v24482, N.v24482.
  unfold R.v6, N.v6.
  rewrite !state_r879_nr_5F879.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r879_nr_5F879 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24483 (s : N.State) (i : N.Inputs) :
  R.v24483 (state s) (inputs i) = Zmod.unsigned (N.v24483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24483 s i)) at 1.
  unfold R.v24483, N.v24483.
  unfold R.v6, N.v6.
  rewrite ?node_9107.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24484 (s : N.State) (i : N.Inputs) :
  R.v24484 (state s) (inputs i) = Zmod.unsigned (N.v24484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24484 s i)) at 1.
  unfold R.v24484, N.v24484.
  rewrite ?node_24482.
  rewrite ?node_24483.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24485 (s : N.State) (i : N.Inputs) :
  R.v24485 (state s) (inputs i) = Zmod.unsigned (N.v24485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24485 s i)) at 1.
  unfold R.v24485, N.v24485.
  unfold R.v16484, N.v16484.
  rewrite ?node_24484.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24486 (s : N.State) (i : N.Inputs) :
  R.v24486 (state s) (inputs i) = Zmod.unsigned (N.v24486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24486 s i)) at 1.
  unfold R.v24486, N.v24486.
  rewrite ?node_24481.
  rewrite ?node_24485.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24487 (s : N.State) (i : N.Inputs) :
  R.v24487 (state s) (inputs i) = Zmod.unsigned (N.v24487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24487 s i)) at 1.
  unfold R.v24487, N.v24487.
  unfold R.v6, N.v6.
  rewrite ?node_24486.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24488 (s : N.State) (i : N.Inputs) :
  R.v24488 (state s) (inputs i) = Zmod.unsigned (N.v24488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24488 s i)) at 1.
  unfold R.v24488, N.v24488.
  rewrite ?node_9112.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24489 (s : N.State) (i : N.Inputs) :
  R.v24489 (state s) (inputs i) = Zmod.unsigned (N.v24489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24489 s i)) at 1.
  unfold R.v24489, N.v24489.
  unfold R.v6, N.v6.
  rewrite ?node_9305.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24490 (s : N.State) (i : N.Inputs) :
  R.v24490 (state s) (inputs i) = Zmod.unsigned (N.v24490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24490 s i)) at 1.
  unfold R.v24490, N.v24490.
  rewrite ?node_24488.
  rewrite ?node_24489.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24491 (s : N.State) (i : N.Inputs) :
  R.v24491 (state s) (inputs i) = Zmod.unsigned (N.v24491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24491 s i)) at 1.
  unfold R.v24491, N.v24491.
  rewrite ?node_24487.
  rewrite ?node_24490.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24492 (s : N.State) (i : N.Inputs) :
  R.v24492 (state s) (inputs i) = Zmod.unsigned (N.v24492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24492 s i)) at 1.
  unfold R.v24492, N.v24492.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24493 (s : N.State) (i : N.Inputs) :
  R.v24493 (state s) (inputs i) = Zmod.unsigned (N.v24493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24493 s i)) at 1.
  unfold R.v24493, N.v24493.
  rewrite ?node_9119.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24494 (s : N.State) (i : N.Inputs) :
  R.v24494 (state s) (inputs i) = Zmod.unsigned (N.v24494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24494 s i)) at 1.
  unfold R.v24494, N.v24494.
  unfold R.v16463, N.v16463.
  rewrite !state_r883_nr_5F883.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r883_nr_5F883 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24495 (s : N.State) (i : N.Inputs) :
  R.v24495 (state s) (inputs i) = Zmod.unsigned (N.v24495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24495 s i)) at 1.
  unfold R.v24495, N.v24495.
  unfold R.v16463, N.v16463.
  rewrite !state_r882_nr_5F882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r882_nr_5F882 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24496 (s : N.State) (i : N.Inputs) :
  R.v24496 (state s) (inputs i) = Zmod.unsigned (N.v24496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24496 s i)) at 1.
  unfold R.v24496, N.v24496.
  unfold R.v6, N.v6.
  rewrite !state_r881_nr_5F881.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r881_nr_5F881 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24497 (s : N.State) (i : N.Inputs) :
  R.v24497 (state s) (inputs i) = Zmod.unsigned (N.v24497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24497 s i)) at 1.
  unfold R.v24497, N.v24497.
  unfold R.v6, N.v6.
  rewrite !state_r880_nr_5F880.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r880_nr_5F880 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24498 (s : N.State) (i : N.Inputs) :
  R.v24498 (state s) (inputs i) = Zmod.unsigned (N.v24498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24498 s i)) at 1.
  unfold R.v24498, N.v24498.
  rewrite ?node_24496.
  rewrite ?node_24497.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24499 (s : N.State) (i : N.Inputs) :
  R.v24499 (state s) (inputs i) = Zmod.unsigned (N.v24499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24499 s i)) at 1.
  unfold R.v24499, N.v24499.
  unfold R.v16484, N.v16484.
  rewrite ?node_24498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24500 (s : N.State) (i : N.Inputs) :
  R.v24500 (state s) (inputs i) = Zmod.unsigned (N.v24500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24500 s i)) at 1.
  unfold R.v24500, N.v24500.
  rewrite ?node_24493.
  rewrite ?node_24494.
  rewrite ?node_24495.
  rewrite ?node_24499.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24501 (s : N.State) (i : N.Inputs) :
  R.v24501 (state s) (inputs i) = Zmod.unsigned (N.v24501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24501 s i)) at 1.
  unfold R.v24501, N.v24501.
  unfold R.v6, N.v6.
  rewrite ?node_24500.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24502 (s : N.State) (i : N.Inputs) :
  R.v24502 (state s) (inputs i) = Zmod.unsigned (N.v24502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24502 s i)) at 1.
  unfold R.v24502, N.v24502.
  rewrite ?node_9120.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24503 (s : N.State) (i : N.Inputs) :
  R.v24503 (state s) (inputs i) = Zmod.unsigned (N.v24503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24503 s i)) at 1.
  unfold R.v24503, N.v24503.
  unfold R.v6, N.v6.
  rewrite ?node_9259.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24504 (s : N.State) (i : N.Inputs) :
  R.v24504 (state s) (inputs i) = Zmod.unsigned (N.v24504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24504 s i)) at 1.
  unfold R.v24504, N.v24504.
  unfold R.v6, N.v6.
  rewrite ?node_9309.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24505 (s : N.State) (i : N.Inputs) :
  R.v24505 (state s) (inputs i) = Zmod.unsigned (N.v24505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24505 s i)) at 1.
  unfold R.v24505, N.v24505.
  rewrite ?node_24502.
  rewrite ?node_24503.
  rewrite ?node_24504.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24506 (s : N.State) (i : N.Inputs) :
  R.v24506 (state s) (inputs i) = Zmod.unsigned (N.v24506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24506 s i)) at 1.
  unfold R.v24506, N.v24506.
  rewrite ?node_24501.
  rewrite ?node_24505.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24507 (s : N.State) (i : N.Inputs) :
  R.v24507 (state s) (inputs i) = Zmod.unsigned (N.v24507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24507 s i)) at 1.
  unfold R.v24507, N.v24507.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24508 (s : N.State) (i : N.Inputs) :
  R.v24508 (state s) (inputs i) = Zmod.unsigned (N.v24508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24508 s i)) at 1.
  unfold R.v24508, N.v24508.
  unfold R.v16463, N.v16463.
  rewrite !state_r882_nr_5F882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r882_nr_5F882 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24509 (s : N.State) (i : N.Inputs) :
  R.v24509 (state s) (inputs i) = Zmod.unsigned (N.v24509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24509 s i)) at 1.
  unfold R.v24509, N.v24509.
  unfold R.v6, N.v6.
  rewrite !state_r881_nr_5F881.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r881_nr_5F881 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24510 (s : N.State) (i : N.Inputs) :
  R.v24510 (state s) (inputs i) = Zmod.unsigned (N.v24510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24510 s i)) at 1.
  unfold R.v24510, N.v24510.
  unfold R.v6, N.v6.
  rewrite !state_r880_nr_5F880.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r880_nr_5F880 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24511 (s : N.State) (i : N.Inputs) :
  R.v24511 (state s) (inputs i) = Zmod.unsigned (N.v24511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24511 s i)) at 1.
  unfold R.v24511, N.v24511.
  rewrite ?node_24509.
  rewrite ?node_24510.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24512 (s : N.State) (i : N.Inputs) :
  R.v24512 (state s) (inputs i) = Zmod.unsigned (N.v24512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24512 s i)) at 1.
  unfold R.v24512, N.v24512.
  unfold R.v16484, N.v16484.
  rewrite ?node_24511.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24513 (s : N.State) (i : N.Inputs) :
  R.v24513 (state s) (inputs i) = Zmod.unsigned (N.v24513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24513 s i)) at 1.
  unfold R.v24513, N.v24513.
  rewrite ?node_24508.
  rewrite ?node_24512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24514 (s : N.State) (i : N.Inputs) :
  R.v24514 (state s) (inputs i) = Zmod.unsigned (N.v24514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24514 s i)) at 1.
  unfold R.v24514, N.v24514.
  unfold R.v6, N.v6.
  rewrite ?node_24513.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24515 (s : N.State) (i : N.Inputs) :
  R.v24515 (state s) (inputs i) = Zmod.unsigned (N.v24515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24515 s i)) at 1.
  unfold R.v24515, N.v24515.
  rewrite ?node_9115.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24516 (s : N.State) (i : N.Inputs) :
  R.v24516 (state s) (inputs i) = Zmod.unsigned (N.v24516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24516 s i)) at 1.
  unfold R.v24516, N.v24516.
  unfold R.v6, N.v6.
  rewrite ?node_9259.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24517 (s : N.State) (i : N.Inputs) :
  R.v24517 (state s) (inputs i) = Zmod.unsigned (N.v24517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24517 s i)) at 1.
  unfold R.v24517, N.v24517.
  rewrite ?node_24515.
  rewrite ?node_24516.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24518 (s : N.State) (i : N.Inputs) :
  R.v24518 (state s) (inputs i) = Zmod.unsigned (N.v24518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24518 s i)) at 1.
  unfold R.v24518, N.v24518.
  rewrite ?node_24514.
  rewrite ?node_24517.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24519 (s : N.State) (i : N.Inputs) :
  R.v24519 (state s) (inputs i) = Zmod.unsigned (N.v24519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24519 s i)) at 1.
  unfold R.v24519, N.v24519.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24520 (s : N.State) (i : N.Inputs) :
  R.v24520 (state s) (inputs i) = Zmod.unsigned (N.v24520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24520 s i)) at 1.
  unfold R.v24520, N.v24520.
  rewrite ?node_9119.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24521 (s : N.State) (i : N.Inputs) :
  R.v24521 (state s) (inputs i) = Zmod.unsigned (N.v24521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24521 s i)) at 1.
  unfold R.v24521, N.v24521.
  unfold R.v6, N.v6.
  rewrite !state_r883_nr_5F883.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r883_nr_5F883 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24522 (s : N.State) (i : N.Inputs) :
  R.v24522 (state s) (inputs i) = Zmod.unsigned (N.v24522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24522 s i)) at 1.
  unfold R.v24522, N.v24522.
  unfold R.v6, N.v6.
  rewrite ?node_9115.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24523 (s : N.State) (i : N.Inputs) :
  R.v24523 (state s) (inputs i) = Zmod.unsigned (N.v24523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24523 s i)) at 1.
  unfold R.v24523, N.v24523.
  rewrite ?node_24521.
  rewrite ?node_24522.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24524 (s : N.State) (i : N.Inputs) :
  R.v24524 (state s) (inputs i) = Zmod.unsigned (N.v24524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24524 s i)) at 1.
  unfold R.v24524, N.v24524.
  unfold R.v16484, N.v16484.
  rewrite ?node_24523.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24525 (s : N.State) (i : N.Inputs) :
  R.v24525 (state s) (inputs i) = Zmod.unsigned (N.v24525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24525 s i)) at 1.
  unfold R.v24525, N.v24525.
  rewrite ?node_24520.
  rewrite ?node_24524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24526 (s : N.State) (i : N.Inputs) :
  R.v24526 (state s) (inputs i) = Zmod.unsigned (N.v24526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24526 s i)) at 1.
  unfold R.v24526, N.v24526.
  unfold R.v6, N.v6.
  rewrite ?node_24525.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24527 (s : N.State) (i : N.Inputs) :
  R.v24527 (state s) (inputs i) = Zmod.unsigned (N.v24527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24527 s i)) at 1.
  unfold R.v24527, N.v24527.
  rewrite ?node_9120.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24528 (s : N.State) (i : N.Inputs) :
  R.v24528 (state s) (inputs i) = Zmod.unsigned (N.v24528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24528 s i)) at 1.
  unfold R.v24528, N.v24528.
  unfold R.v6, N.v6.
  rewrite ?node_9309.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24529 (s : N.State) (i : N.Inputs) :
  R.v24529 (state s) (inputs i) = Zmod.unsigned (N.v24529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24529 s i)) at 1.
  unfold R.v24529, N.v24529.
  rewrite ?node_24527.
  rewrite ?node_24528.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24530 (s : N.State) (i : N.Inputs) :
  R.v24530 (state s) (inputs i) = Zmod.unsigned (N.v24530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24530 s i)) at 1.
  unfold R.v24530, N.v24530.
  rewrite ?node_24526.
  rewrite ?node_24529.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24531 (s : N.State) (i : N.Inputs) :
  R.v24531 (state s) (inputs i) = Zmod.unsigned (N.v24531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24531 s i)) at 1.
  unfold R.v24531, N.v24531.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24532 (s : N.State) (i : N.Inputs) :
  R.v24532 (state s) (inputs i) = Zmod.unsigned (N.v24532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24532 s i)) at 1.
  unfold R.v24532, N.v24532.
  rewrite ?node_9131.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24533 (s : N.State) (i : N.Inputs) :
  R.v24533 (state s) (inputs i) = Zmod.unsigned (N.v24533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24533 s i)) at 1.
  unfold R.v24533, N.v24533.
  unfold R.v16463, N.v16463.
  rewrite !state_r887_nr_5F887.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r887_nr_5F887 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24534 (s : N.State) (i : N.Inputs) :
  R.v24534 (state s) (inputs i) = Zmod.unsigned (N.v24534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24534 s i)) at 1.
  unfold R.v24534, N.v24534.
  unfold R.v16463, N.v16463.
  rewrite !state_r886_nr_5F886.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r886_nr_5F886 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24535 (s : N.State) (i : N.Inputs) :
  R.v24535 (state s) (inputs i) = Zmod.unsigned (N.v24535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24535 s i)) at 1.
  unfold R.v24535, N.v24535.
  unfold R.v6, N.v6.
  rewrite !state_r885_nr_5F885.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r885_nr_5F885 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24536 (s : N.State) (i : N.Inputs) :
  R.v24536 (state s) (inputs i) = Zmod.unsigned (N.v24536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24536 s i)) at 1.
  unfold R.v24536, N.v24536.
  unfold R.v6, N.v6.
  rewrite !state_r884_nr_5F884.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r884_nr_5F884 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24537 (s : N.State) (i : N.Inputs) :
  R.v24537 (state s) (inputs i) = Zmod.unsigned (N.v24537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24537 s i)) at 1.
  unfold R.v24537, N.v24537.
  rewrite ?node_24535.
  rewrite ?node_24536.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24538 (s : N.State) (i : N.Inputs) :
  R.v24538 (state s) (inputs i) = Zmod.unsigned (N.v24538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24538 s i)) at 1.
  unfold R.v24538, N.v24538.
  unfold R.v16484, N.v16484.
  rewrite ?node_24537.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24539 (s : N.State) (i : N.Inputs) :
  R.v24539 (state s) (inputs i) = Zmod.unsigned (N.v24539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24539 s i)) at 1.
  unfold R.v24539, N.v24539.
  rewrite ?node_24532.
  rewrite ?node_24533.
  rewrite ?node_24534.
  rewrite ?node_24538.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24540 (s : N.State) (i : N.Inputs) :
  R.v24540 (state s) (inputs i) = Zmod.unsigned (N.v24540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24540 s i)) at 1.
  unfold R.v24540, N.v24540.
  unfold R.v6, N.v6.
  rewrite ?node_24539.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24541 (s : N.State) (i : N.Inputs) :
  R.v24541 (state s) (inputs i) = Zmod.unsigned (N.v24541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24541 s i)) at 1.
  unfold R.v24541, N.v24541.
  rewrite ?node_9132.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24542 (s : N.State) (i : N.Inputs) :
  R.v24542 (state s) (inputs i) = Zmod.unsigned (N.v24542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24542 s i)) at 1.
  unfold R.v24542, N.v24542.
  unfold R.v6, N.v6.
  rewrite ?node_9271.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24543 (s : N.State) (i : N.Inputs) :
  R.v24543 (state s) (inputs i) = Zmod.unsigned (N.v24543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24543 s i)) at 1.
  unfold R.v24543, N.v24543.
  unfold R.v6, N.v6.
  rewrite ?node_9318.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24544 (s : N.State) (i : N.Inputs) :
  R.v24544 (state s) (inputs i) = Zmod.unsigned (N.v24544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24544 s i)) at 1.
  unfold R.v24544, N.v24544.
  rewrite ?node_24541.
  rewrite ?node_24542.
  rewrite ?node_24543.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24545 (s : N.State) (i : N.Inputs) :
  R.v24545 (state s) (inputs i) = Zmod.unsigned (N.v24545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24545 s i)) at 1.
  unfold R.v24545, N.v24545.
  rewrite ?node_24540.
  rewrite ?node_24544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24546 (s : N.State) (i : N.Inputs) :
  R.v24546 (state s) (inputs i) = Zmod.unsigned (N.v24546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24546 s i)) at 1.
  unfold R.v24546, N.v24546.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24547 (s : N.State) (i : N.Inputs) :
  R.v24547 (state s) (inputs i) = Zmod.unsigned (N.v24547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24547 s i)) at 1.
  unfold R.v24547, N.v24547.
  unfold R.v16463, N.v16463.
  rewrite !state_r886_nr_5F886.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r886_nr_5F886 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24548 (s : N.State) (i : N.Inputs) :
  R.v24548 (state s) (inputs i) = Zmod.unsigned (N.v24548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24548 s i)) at 1.
  unfold R.v24548, N.v24548.
  unfold R.v6, N.v6.
  rewrite !state_r885_nr_5F885.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r885_nr_5F885 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24549 (s : N.State) (i : N.Inputs) :
  R.v24549 (state s) (inputs i) = Zmod.unsigned (N.v24549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24549 s i)) at 1.
  unfold R.v24549, N.v24549.
  unfold R.v6, N.v6.
  rewrite !state_r884_nr_5F884.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r884_nr_5F884 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24550 (s : N.State) (i : N.Inputs) :
  R.v24550 (state s) (inputs i) = Zmod.unsigned (N.v24550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24550 s i)) at 1.
  unfold R.v24550, N.v24550.
  rewrite ?node_24548.
  rewrite ?node_24549.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24551 (s : N.State) (i : N.Inputs) :
  R.v24551 (state s) (inputs i) = Zmod.unsigned (N.v24551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24551 s i)) at 1.
  unfold R.v24551, N.v24551.
  unfold R.v16484, N.v16484.
  rewrite ?node_24550.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24552 (s : N.State) (i : N.Inputs) :
  R.v24552 (state s) (inputs i) = Zmod.unsigned (N.v24552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24552 s i)) at 1.
  unfold R.v24552, N.v24552.
  rewrite ?node_24547.
  rewrite ?node_24551.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24553 (s : N.State) (i : N.Inputs) :
  R.v24553 (state s) (inputs i) = Zmod.unsigned (N.v24553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24553 s i)) at 1.
  unfold R.v24553, N.v24553.
  unfold R.v6, N.v6.
  rewrite ?node_24552.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24554 (s : N.State) (i : N.Inputs) :
  R.v24554 (state s) (inputs i) = Zmod.unsigned (N.v24554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24554 s i)) at 1.
  unfold R.v24554, N.v24554.
  rewrite ?node_9127.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24555 (s : N.State) (i : N.Inputs) :
  R.v24555 (state s) (inputs i) = Zmod.unsigned (N.v24555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24555 s i)) at 1.
  unfold R.v24555, N.v24555.
  unfold R.v6, N.v6.
  rewrite ?node_9271.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24556 (s : N.State) (i : N.Inputs) :
  R.v24556 (state s) (inputs i) = Zmod.unsigned (N.v24556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24556 s i)) at 1.
  unfold R.v24556, N.v24556.
  rewrite ?node_24554.
  rewrite ?node_24555.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24557 (s : N.State) (i : N.Inputs) :
  R.v24557 (state s) (inputs i) = Zmod.unsigned (N.v24557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24557 s i)) at 1.
  unfold R.v24557, N.v24557.
  rewrite ?node_24553.
  rewrite ?node_24556.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24558 (s : N.State) (i : N.Inputs) :
  R.v24558 (state s) (inputs i) = Zmod.unsigned (N.v24558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24558 s i)) at 1.
  unfold R.v24558, N.v24558.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24559 (s : N.State) (i : N.Inputs) :
  R.v24559 (state s) (inputs i) = Zmod.unsigned (N.v24559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24559 s i)) at 1.
  unfold R.v24559, N.v24559.
  rewrite ?node_9131.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24560 (s : N.State) (i : N.Inputs) :
  R.v24560 (state s) (inputs i) = Zmod.unsigned (N.v24560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24560 s i)) at 1.
  unfold R.v24560, N.v24560.
  unfold R.v6, N.v6.
  rewrite !state_r887_nr_5F887.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r887_nr_5F887 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24561 (s : N.State) (i : N.Inputs) :
  R.v24561 (state s) (inputs i) = Zmod.unsigned (N.v24561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24561 s i)) at 1.
  unfold R.v24561, N.v24561.
  unfold R.v6, N.v6.
  rewrite ?node_9127.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24562 (s : N.State) (i : N.Inputs) :
  R.v24562 (state s) (inputs i) = Zmod.unsigned (N.v24562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24562 s i)) at 1.
  unfold R.v24562, N.v24562.
  rewrite ?node_24560.
  rewrite ?node_24561.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24563 (s : N.State) (i : N.Inputs) :
  R.v24563 (state s) (inputs i) = Zmod.unsigned (N.v24563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24563 s i)) at 1.
  unfold R.v24563, N.v24563.
  unfold R.v16484, N.v16484.
  rewrite ?node_24562.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24564 (s : N.State) (i : N.Inputs) :
  R.v24564 (state s) (inputs i) = Zmod.unsigned (N.v24564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24564 s i)) at 1.
  unfold R.v24564, N.v24564.
  rewrite ?node_24559.
  rewrite ?node_24563.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24565 (s : N.State) (i : N.Inputs) :
  R.v24565 (state s) (inputs i) = Zmod.unsigned (N.v24565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24565 s i)) at 1.
  unfold R.v24565, N.v24565.
  unfold R.v6, N.v6.
  rewrite ?node_24564.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24566 (s : N.State) (i : N.Inputs) :
  R.v24566 (state s) (inputs i) = Zmod.unsigned (N.v24566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24566 s i)) at 1.
  unfold R.v24566, N.v24566.
  rewrite ?node_9132.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24567 (s : N.State) (i : N.Inputs) :
  R.v24567 (state s) (inputs i) = Zmod.unsigned (N.v24567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24567 s i)) at 1.
  unfold R.v24567, N.v24567.
  unfold R.v6, N.v6.
  rewrite ?node_9318.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24568 (s : N.State) (i : N.Inputs) :
  R.v24568 (state s) (inputs i) = Zmod.unsigned (N.v24568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24568 s i)) at 1.
  unfold R.v24568, N.v24568.
  rewrite ?node_24566.
  rewrite ?node_24567.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24569 (s : N.State) (i : N.Inputs) :
  R.v24569 (state s) (inputs i) = Zmod.unsigned (N.v24569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24569 s i)) at 1.
  unfold R.v24569, N.v24569.
  rewrite ?node_24565.
  rewrite ?node_24568.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24570 (s : N.State) (i : N.Inputs) :
  R.v24570 (state s) (inputs i) = Zmod.unsigned (N.v24570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24570 s i)) at 1.
  unfold R.v24570, N.v24570.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24571 (s : N.State) (i : N.Inputs) :
  R.v24571 (state s) (inputs i) = Zmod.unsigned (N.v24571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24571 s i)) at 1.
  unfold R.v24571, N.v24571.
  rewrite ?node_9138.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24572 (s : N.State) (i : N.Inputs) :
  R.v24572 (state s) (inputs i) = Zmod.unsigned (N.v24572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24572 s i)) at 1.
  unfold R.v24572, N.v24572.
  unfold R.v16463, N.v16463.
  rewrite !state_r891_nr_5F891.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r891_nr_5F891 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24573 (s : N.State) (i : N.Inputs) :
  R.v24573 (state s) (inputs i) = Zmod.unsigned (N.v24573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24573 s i)) at 1.
  unfold R.v24573, N.v24573.
  unfold R.v16463, N.v16463.
  rewrite !state_r890_nr_5F890.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r890_nr_5F890 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24574 (s : N.State) (i : N.Inputs) :
  R.v24574 (state s) (inputs i) = Zmod.unsigned (N.v24574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24574 s i)) at 1.
  unfold R.v24574, N.v24574.
  unfold R.v6, N.v6.
  rewrite !state_r889_nr_5F889.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r889_nr_5F889 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24575 (s : N.State) (i : N.Inputs) :
  R.v24575 (state s) (inputs i) = Zmod.unsigned (N.v24575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24575 s i)) at 1.
  unfold R.v24575, N.v24575.
  unfold R.v6, N.v6.
  rewrite !state_r888_nr_5F888.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r888_nr_5F888 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24576 (s : N.State) (i : N.Inputs) :
  R.v24576 (state s) (inputs i) = Zmod.unsigned (N.v24576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24576 s i)) at 1.
  unfold R.v24576, N.v24576.
  rewrite ?node_24574.
  rewrite ?node_24575.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24577 (s : N.State) (i : N.Inputs) :
  R.v24577 (state s) (inputs i) = Zmod.unsigned (N.v24577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24577 s i)) at 1.
  unfold R.v24577, N.v24577.
  unfold R.v16484, N.v16484.
  rewrite ?node_24576.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24578 (s : N.State) (i : N.Inputs) :
  R.v24578 (state s) (inputs i) = Zmod.unsigned (N.v24578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24578 s i)) at 1.
  unfold R.v24578, N.v24578.
  rewrite ?node_24571.
  rewrite ?node_24572.
  rewrite ?node_24573.
  rewrite ?node_24577.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24579 (s : N.State) (i : N.Inputs) :
  R.v24579 (state s) (inputs i) = Zmod.unsigned (N.v24579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24579 s i)) at 1.
  unfold R.v24579, N.v24579.
  unfold R.v6, N.v6.
  rewrite ?node_24578.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24580 (s : N.State) (i : N.Inputs) :
  R.v24580 (state s) (inputs i) = Zmod.unsigned (N.v24580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24580 s i)) at 1.
  unfold R.v24580, N.v24580.
  rewrite ?node_9139.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24581 (s : N.State) (i : N.Inputs) :
  R.v24581 (state s) (inputs i) = Zmod.unsigned (N.v24581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24581 s i)) at 1.
  unfold R.v24581, N.v24581.
  unfold R.v6, N.v6.
  rewrite ?node_9278.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24582 (s : N.State) (i : N.Inputs) :
  R.v24582 (state s) (inputs i) = Zmod.unsigned (N.v24582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24582 s i)) at 1.
  unfold R.v24582, N.v24582.
  unfold R.v6, N.v6.
  rewrite ?node_9321.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24583 (s : N.State) (i : N.Inputs) :
  R.v24583 (state s) (inputs i) = Zmod.unsigned (N.v24583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24583 s i)) at 1.
  unfold R.v24583, N.v24583.
  rewrite ?node_24580.
  rewrite ?node_24581.
  rewrite ?node_24582.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24584 (s : N.State) (i : N.Inputs) :
  R.v24584 (state s) (inputs i) = Zmod.unsigned (N.v24584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24584 s i)) at 1.
  unfold R.v24584, N.v24584.
  rewrite ?node_24579.
  rewrite ?node_24583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24585 (s : N.State) (i : N.Inputs) :
  R.v24585 (state s) (inputs i) = Zmod.unsigned (N.v24585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24585 s i)) at 1.
  unfold R.v24585, N.v24585.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24586 (s : N.State) (i : N.Inputs) :
  R.v24586 (state s) (inputs i) = Zmod.unsigned (N.v24586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24586 s i)) at 1.
  unfold R.v24586, N.v24586.
  unfold R.v16463, N.v16463.
  rewrite !state_r890_nr_5F890.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r890_nr_5F890 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24587 (s : N.State) (i : N.Inputs) :
  R.v24587 (state s) (inputs i) = Zmod.unsigned (N.v24587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24587 s i)) at 1.
  unfold R.v24587, N.v24587.
  unfold R.v6, N.v6.
  rewrite !state_r889_nr_5F889.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r889_nr_5F889 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24588 (s : N.State) (i : N.Inputs) :
  R.v24588 (state s) (inputs i) = Zmod.unsigned (N.v24588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24588 s i)) at 1.
  unfold R.v24588, N.v24588.
  unfold R.v6, N.v6.
  rewrite !state_r888_nr_5F888.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r888_nr_5F888 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24589 (s : N.State) (i : N.Inputs) :
  R.v24589 (state s) (inputs i) = Zmod.unsigned (N.v24589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24589 s i)) at 1.
  unfold R.v24589, N.v24589.
  rewrite ?node_24587.
  rewrite ?node_24588.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24590 (s : N.State) (i : N.Inputs) :
  R.v24590 (state s) (inputs i) = Zmod.unsigned (N.v24590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24590 s i)) at 1.
  unfold R.v24590, N.v24590.
  unfold R.v16484, N.v16484.
  rewrite ?node_24589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24591 (s : N.State) (i : N.Inputs) :
  R.v24591 (state s) (inputs i) = Zmod.unsigned (N.v24591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24591 s i)) at 1.
  unfold R.v24591, N.v24591.
  rewrite ?node_24586.
  rewrite ?node_24590.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24592 (s : N.State) (i : N.Inputs) :
  R.v24592 (state s) (inputs i) = Zmod.unsigned (N.v24592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24592 s i)) at 1.
  unfold R.v24592, N.v24592.
  unfold R.v6, N.v6.
  rewrite ?node_24591.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24593 (s : N.State) (i : N.Inputs) :
  R.v24593 (state s) (inputs i) = Zmod.unsigned (N.v24593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24593 s i)) at 1.
  unfold R.v24593, N.v24593.
  rewrite ?node_9134.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24594 (s : N.State) (i : N.Inputs) :
  R.v24594 (state s) (inputs i) = Zmod.unsigned (N.v24594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24594 s i)) at 1.
  unfold R.v24594, N.v24594.
  unfold R.v6, N.v6.
  rewrite ?node_9278.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24595 (s : N.State) (i : N.Inputs) :
  R.v24595 (state s) (inputs i) = Zmod.unsigned (N.v24595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24595 s i)) at 1.
  unfold R.v24595, N.v24595.
  rewrite ?node_24593.
  rewrite ?node_24594.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24596 (s : N.State) (i : N.Inputs) :
  R.v24596 (state s) (inputs i) = Zmod.unsigned (N.v24596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24596 s i)) at 1.
  unfold R.v24596, N.v24596.
  rewrite ?node_24592.
  rewrite ?node_24595.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24597 (s : N.State) (i : N.Inputs) :
  R.v24597 (state s) (inputs i) = Zmod.unsigned (N.v24597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24597 s i)) at 1.
  unfold R.v24597, N.v24597.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24598 (s : N.State) (i : N.Inputs) :
  R.v24598 (state s) (inputs i) = Zmod.unsigned (N.v24598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24598 s i)) at 1.
  unfold R.v24598, N.v24598.
  rewrite ?node_9138.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24599 (s : N.State) (i : N.Inputs) :
  R.v24599 (state s) (inputs i) = Zmod.unsigned (N.v24599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24599 s i)) at 1.
  unfold R.v24599, N.v24599.
  unfold R.v6, N.v6.
  rewrite !state_r891_nr_5F891.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r891_nr_5F891 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24600 (s : N.State) (i : N.Inputs) :
  R.v24600 (state s) (inputs i) = Zmod.unsigned (N.v24600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24600 s i)) at 1.
  unfold R.v24600, N.v24600.
  unfold R.v6, N.v6.
  rewrite ?node_9134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24601 (s : N.State) (i : N.Inputs) :
  R.v24601 (state s) (inputs i) = Zmod.unsigned (N.v24601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24601 s i)) at 1.
  unfold R.v24601, N.v24601.
  rewrite ?node_24599.
  rewrite ?node_24600.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24602 (s : N.State) (i : N.Inputs) :
  R.v24602 (state s) (inputs i) = Zmod.unsigned (N.v24602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24602 s i)) at 1.
  unfold R.v24602, N.v24602.
  unfold R.v16484, N.v16484.
  rewrite ?node_24601.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24603 (s : N.State) (i : N.Inputs) :
  R.v24603 (state s) (inputs i) = Zmod.unsigned (N.v24603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24603 s i)) at 1.
  unfold R.v24603, N.v24603.
  rewrite ?node_24598.
  rewrite ?node_24602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24604 (s : N.State) (i : N.Inputs) :
  R.v24604 (state s) (inputs i) = Zmod.unsigned (N.v24604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24604 s i)) at 1.
  unfold R.v24604, N.v24604.
  unfold R.v6, N.v6.
  rewrite ?node_24603.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24605 (s : N.State) (i : N.Inputs) :
  R.v24605 (state s) (inputs i) = Zmod.unsigned (N.v24605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24605 s i)) at 1.
  unfold R.v24605, N.v24605.
  rewrite ?node_9139.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24606 (s : N.State) (i : N.Inputs) :
  R.v24606 (state s) (inputs i) = Zmod.unsigned (N.v24606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24606 s i)) at 1.
  unfold R.v24606, N.v24606.
  unfold R.v6, N.v6.
  rewrite ?node_9321.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24607 (s : N.State) (i : N.Inputs) :
  R.v24607 (state s) (inputs i) = Zmod.unsigned (N.v24607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24607 s i)) at 1.
  unfold R.v24607, N.v24607.
  rewrite ?node_24605.
  rewrite ?node_24606.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24608 (s : N.State) (i : N.Inputs) :
  R.v24608 (state s) (inputs i) = Zmod.unsigned (N.v24608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24608 s i)) at 1.
  unfold R.v24608, N.v24608.
  rewrite ?node_24604.
  rewrite ?node_24607.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24609 (s : N.State) (i : N.Inputs) :
  R.v24609 (state s) (inputs i) = Zmod.unsigned (N.v24609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24609 s i)) at 1.
  unfold R.v24609, N.v24609.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24610 (s : N.State) (i : N.Inputs) :
  R.v24610 (state s) (inputs i) = Zmod.unsigned (N.v24610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24610 s i)) at 1.
  unfold R.v24610, N.v24610.
  rewrite ?node_9146.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24611 (s : N.State) (i : N.Inputs) :
  R.v24611 (state s) (inputs i) = Zmod.unsigned (N.v24611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24611 s i)) at 1.
  unfold R.v24611, N.v24611.
  unfold R.v16463, N.v16463.
  rewrite !state_r895_nr_5F895.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r895_nr_5F895 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24612 (s : N.State) (i : N.Inputs) :
  R.v24612 (state s) (inputs i) = Zmod.unsigned (N.v24612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24612 s i)) at 1.
  unfold R.v24612, N.v24612.
  unfold R.v16463, N.v16463.
  rewrite !state_r894_nr_5F894.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r894_nr_5F894 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24613 (s : N.State) (i : N.Inputs) :
  R.v24613 (state s) (inputs i) = Zmod.unsigned (N.v24613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24613 s i)) at 1.
  unfold R.v24613, N.v24613.
  unfold R.v6, N.v6.
  rewrite !state_r893_nr_5F893.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r893_nr_5F893 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24614 (s : N.State) (i : N.Inputs) :
  R.v24614 (state s) (inputs i) = Zmod.unsigned (N.v24614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24614 s i)) at 1.
  unfold R.v24614, N.v24614.
  unfold R.v6, N.v6.
  rewrite !state_r892_nr_5F892.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r892_nr_5F892 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24615 (s : N.State) (i : N.Inputs) :
  R.v24615 (state s) (inputs i) = Zmod.unsigned (N.v24615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24615 s i)) at 1.
  unfold R.v24615, N.v24615.
  rewrite ?node_24613.
  rewrite ?node_24614.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24616 (s : N.State) (i : N.Inputs) :
  R.v24616 (state s) (inputs i) = Zmod.unsigned (N.v24616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24616 s i)) at 1.
  unfold R.v24616, N.v24616.
  unfold R.v16484, N.v16484.
  rewrite ?node_24615.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24617 (s : N.State) (i : N.Inputs) :
  R.v24617 (state s) (inputs i) = Zmod.unsigned (N.v24617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24617 s i)) at 1.
  unfold R.v24617, N.v24617.
  rewrite ?node_24610.
  rewrite ?node_24611.
  rewrite ?node_24612.
  rewrite ?node_24616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24618 (s : N.State) (i : N.Inputs) :
  R.v24618 (state s) (inputs i) = Zmod.unsigned (N.v24618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24618 s i)) at 1.
  unfold R.v24618, N.v24618.
  unfold R.v6, N.v6.
  rewrite ?node_24617.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24619 (s : N.State) (i : N.Inputs) :
  R.v24619 (state s) (inputs i) = Zmod.unsigned (N.v24619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24619 s i)) at 1.
  unfold R.v24619, N.v24619.
  rewrite ?node_9147.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24620 (s : N.State) (i : N.Inputs) :
  R.v24620 (state s) (inputs i) = Zmod.unsigned (N.v24620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24620 s i)) at 1.
  unfold R.v24620, N.v24620.
  unfold R.v6, N.v6.
  rewrite ?node_9286.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24621 (s : N.State) (i : N.Inputs) :
  R.v24621 (state s) (inputs i) = Zmod.unsigned (N.v24621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24621 s i)) at 1.
  unfold R.v24621, N.v24621.
  unfold R.v6, N.v6.
  rewrite ?node_9325.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24622 (s : N.State) (i : N.Inputs) :
  R.v24622 (state s) (inputs i) = Zmod.unsigned (N.v24622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24622 s i)) at 1.
  unfold R.v24622, N.v24622.
  rewrite ?node_24619.
  rewrite ?node_24620.
  rewrite ?node_24621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24623 (s : N.State) (i : N.Inputs) :
  R.v24623 (state s) (inputs i) = Zmod.unsigned (N.v24623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24623 s i)) at 1.
  unfold R.v24623, N.v24623.
  rewrite ?node_24618.
  rewrite ?node_24622.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24624 (s : N.State) (i : N.Inputs) :
  R.v24624 (state s) (inputs i) = Zmod.unsigned (N.v24624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24624 s i)) at 1.
  unfold R.v24624, N.v24624.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24625 (s : N.State) (i : N.Inputs) :
  R.v24625 (state s) (inputs i) = Zmod.unsigned (N.v24625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24625 s i)) at 1.
  unfold R.v24625, N.v24625.
  unfold R.v16463, N.v16463.
  rewrite !state_r894_nr_5F894.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r894_nr_5F894 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24626 (s : N.State) (i : N.Inputs) :
  R.v24626 (state s) (inputs i) = Zmod.unsigned (N.v24626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24626 s i)) at 1.
  unfold R.v24626, N.v24626.
  unfold R.v6, N.v6.
  rewrite !state_r893_nr_5F893.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r893_nr_5F893 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24627 (s : N.State) (i : N.Inputs) :
  R.v24627 (state s) (inputs i) = Zmod.unsigned (N.v24627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24627 s i)) at 1.
  unfold R.v24627, N.v24627.
  unfold R.v6, N.v6.
  rewrite !state_r892_nr_5F892.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r892_nr_5F892 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24628 (s : N.State) (i : N.Inputs) :
  R.v24628 (state s) (inputs i) = Zmod.unsigned (N.v24628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24628 s i)) at 1.
  unfold R.v24628, N.v24628.
  rewrite ?node_24626.
  rewrite ?node_24627.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24629 (s : N.State) (i : N.Inputs) :
  R.v24629 (state s) (inputs i) = Zmod.unsigned (N.v24629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24629 s i)) at 1.
  unfold R.v24629, N.v24629.
  unfold R.v16484, N.v16484.
  rewrite ?node_24628.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24630 (s : N.State) (i : N.Inputs) :
  R.v24630 (state s) (inputs i) = Zmod.unsigned (N.v24630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24630 s i)) at 1.
  unfold R.v24630, N.v24630.
  rewrite ?node_24625.
  rewrite ?node_24629.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24631 (s : N.State) (i : N.Inputs) :
  R.v24631 (state s) (inputs i) = Zmod.unsigned (N.v24631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24631 s i)) at 1.
  unfold R.v24631, N.v24631.
  unfold R.v6, N.v6.
  rewrite ?node_24630.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24632 (s : N.State) (i : N.Inputs) :
  R.v24632 (state s) (inputs i) = Zmod.unsigned (N.v24632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24632 s i)) at 1.
  unfold R.v24632, N.v24632.
  rewrite ?node_9142.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24633 (s : N.State) (i : N.Inputs) :
  R.v24633 (state s) (inputs i) = Zmod.unsigned (N.v24633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24633 s i)) at 1.
  unfold R.v24633, N.v24633.
  unfold R.v6, N.v6.
  rewrite ?node_9286.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24634 (s : N.State) (i : N.Inputs) :
  R.v24634 (state s) (inputs i) = Zmod.unsigned (N.v24634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24634 s i)) at 1.
  unfold R.v24634, N.v24634.
  rewrite ?node_24632.
  rewrite ?node_24633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24635 (s : N.State) (i : N.Inputs) :
  R.v24635 (state s) (inputs i) = Zmod.unsigned (N.v24635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24635 s i)) at 1.
  unfold R.v24635, N.v24635.
  rewrite ?node_24631.
  rewrite ?node_24634.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24636 (s : N.State) (i : N.Inputs) :
  R.v24636 (state s) (inputs i) = Zmod.unsigned (N.v24636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24636 s i)) at 1.
  unfold R.v24636, N.v24636.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24637 (s : N.State) (i : N.Inputs) :
  R.v24637 (state s) (inputs i) = Zmod.unsigned (N.v24637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24637 s i)) at 1.
  unfold R.v24637, N.v24637.
  rewrite ?node_9146.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24638 (s : N.State) (i : N.Inputs) :
  R.v24638 (state s) (inputs i) = Zmod.unsigned (N.v24638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24638 s i)) at 1.
  unfold R.v24638, N.v24638.
  unfold R.v6, N.v6.
  rewrite !state_r895_nr_5F895.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r895_nr_5F895 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24639 (s : N.State) (i : N.Inputs) :
  R.v24639 (state s) (inputs i) = Zmod.unsigned (N.v24639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24639 s i)) at 1.
  unfold R.v24639, N.v24639.
  unfold R.v6, N.v6.
  rewrite ?node_9142.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24640 (s : N.State) (i : N.Inputs) :
  R.v24640 (state s) (inputs i) = Zmod.unsigned (N.v24640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24640 s i)) at 1.
  unfold R.v24640, N.v24640.
  rewrite ?node_24638.
  rewrite ?node_24639.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24641 (s : N.State) (i : N.Inputs) :
  R.v24641 (state s) (inputs i) = Zmod.unsigned (N.v24641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24641 s i)) at 1.
  unfold R.v24641, N.v24641.
  unfold R.v16484, N.v16484.
  rewrite ?node_24640.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24642 (s : N.State) (i : N.Inputs) :
  R.v24642 (state s) (inputs i) = Zmod.unsigned (N.v24642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24642 s i)) at 1.
  unfold R.v24642, N.v24642.
  rewrite ?node_24637.
  rewrite ?node_24641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24643 (s : N.State) (i : N.Inputs) :
  R.v24643 (state s) (inputs i) = Zmod.unsigned (N.v24643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24643 s i)) at 1.
  unfold R.v24643, N.v24643.
  unfold R.v6, N.v6.
  rewrite ?node_24642.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24644 (s : N.State) (i : N.Inputs) :
  R.v24644 (state s) (inputs i) = Zmod.unsigned (N.v24644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24644 s i)) at 1.
  unfold R.v24644, N.v24644.
  rewrite ?node_9147.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24645 (s : N.State) (i : N.Inputs) :
  R.v24645 (state s) (inputs i) = Zmod.unsigned (N.v24645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24645 s i)) at 1.
  unfold R.v24645, N.v24645.
  unfold R.v6, N.v6.
  rewrite ?node_9325.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24646 (s : N.State) (i : N.Inputs) :
  R.v24646 (state s) (inputs i) = Zmod.unsigned (N.v24646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24646 s i)) at 1.
  unfold R.v24646, N.v24646.
  rewrite ?node_24644.
  rewrite ?node_24645.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24647 (s : N.State) (i : N.Inputs) :
  R.v24647 (state s) (inputs i) = Zmod.unsigned (N.v24647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24647 s i)) at 1.
  unfold R.v24647, N.v24647.
  rewrite ?node_24643.
  rewrite ?node_24646.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24648 (s : N.State) (i : N.Inputs) :
  R.v24648 (state s) (inputs i) = Zmod.unsigned (N.v24648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24648 s i)) at 1.
  unfold R.v24648, N.v24648.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24649 (s : N.State) (i : N.Inputs) :
  R.v24649 (state s) (inputs i) = Zmod.unsigned (N.v24649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24649 s i)) at 1.
  unfold R.v24649, N.v24649.
  unfold R.v6, N.v6.
  rewrite !state_r897_nr_5F897.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r897_nr_5F897 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24650 (s : N.State) (i : N.Inputs) :
  R.v24650 (state s) (inputs i) = Zmod.unsigned (N.v24650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24650 s i)) at 1.
  unfold R.v24650, N.v24650.
  unfold R.v6, N.v6.
  rewrite !state_r896_nr_5F896.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r896_nr_5F896 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24651 (s : N.State) (i : N.Inputs) :
  R.v24651 (state s) (inputs i) = Zmod.unsigned (N.v24651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24651 s i)) at 1.
  unfold R.v24651, N.v24651.
  rewrite ?node_24649.
  rewrite ?node_24650.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24652 (s : N.State) (i : N.Inputs) :
  R.v24652 (state s) (inputs i) = Zmod.unsigned (N.v24652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24652 s i)) at 1.
  unfold R.v24652, N.v24652.
  unfold R.v16463, N.v16463.
  rewrite ?node_24651.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24653 (s : N.State) (i : N.Inputs) :
  R.v24653 (state s) (inputs i) = Zmod.unsigned (N.v24653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24653 s i)) at 1.
  unfold R.v24653, N.v24653.
  rewrite ?node_9149.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24654 (s : N.State) (i : N.Inputs) :
  R.v24654 (state s) (inputs i) = Zmod.unsigned (N.v24654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24654 s i)) at 1.
  unfold R.v24654, N.v24654.
  unfold R.v6, N.v6.
  rewrite ?node_9327.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24655 (s : N.State) (i : N.Inputs) :
  R.v24655 (state s) (inputs i) = Zmod.unsigned (N.v24655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24655 s i)) at 1.
  unfold R.v24655, N.v24655.
  rewrite ?node_24653.
  rewrite ?node_24654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24656 (s : N.State) (i : N.Inputs) :
  R.v24656 (state s) (inputs i) = Zmod.unsigned (N.v24656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24656 s i)) at 1.
  unfold R.v24656, N.v24656.
  rewrite ?node_24652.
  rewrite ?node_24655.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24657 (s : N.State) (i : N.Inputs) :
  R.v24657 (state s) (inputs i) = Zmod.unsigned (N.v24657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24657 s i)) at 1.
  unfold R.v24657, N.v24657.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24658 (s : N.State) (i : N.Inputs) :
  R.v24658 (state s) (inputs i) = Zmod.unsigned (N.v24658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24658 s i)) at 1.
  unfold R.v24658, N.v24658.
  rewrite ?node_9236.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24659 (s : N.State) (i : N.Inputs) :
  R.v24659 (state s) (inputs i) = Zmod.unsigned (N.v24659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24659 s i)) at 1.
  unfold R.v24659, N.v24659.
  unfold R.v16463, N.v16463.
  rewrite !state_r901_nr_5F901.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r901_nr_5F901 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24660 (s : N.State) (i : N.Inputs) :
  R.v24660 (state s) (inputs i) = Zmod.unsigned (N.v24660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24660 s i)) at 1.
  unfold R.v24660, N.v24660.
  unfold R.v16463, N.v16463.
  rewrite !state_r900_nr_5F900.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r900_nr_5F900 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24661 (s : N.State) (i : N.Inputs) :
  R.v24661 (state s) (inputs i) = Zmod.unsigned (N.v24661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24661 s i)) at 1.
  unfold R.v24661, N.v24661.
  unfold R.v6, N.v6.
  rewrite !state_r899_nr_5F899.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r899_nr_5F899 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24662 (s : N.State) (i : N.Inputs) :
  R.v24662 (state s) (inputs i) = Zmod.unsigned (N.v24662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24662 s i)) at 1.
  unfold R.v24662, N.v24662.
  unfold R.v6, N.v6.
  rewrite !state_r898_nr_5F898.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r898_nr_5F898 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24663 (s : N.State) (i : N.Inputs) :
  R.v24663 (state s) (inputs i) = Zmod.unsigned (N.v24663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24663 s i)) at 1.
  unfold R.v24663, N.v24663.
  rewrite ?node_24661.
  rewrite ?node_24662.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24664 (s : N.State) (i : N.Inputs) :
  R.v24664 (state s) (inputs i) = Zmod.unsigned (N.v24664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24664 s i)) at 1.
  unfold R.v24664, N.v24664.
  unfold R.v16484, N.v16484.
  rewrite ?node_24663.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24665 (s : N.State) (i : N.Inputs) :
  R.v24665 (state s) (inputs i) = Zmod.unsigned (N.v24665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24665 s i)) at 1.
  unfold R.v24665, N.v24665.
  rewrite ?node_24658.
  rewrite ?node_24659.
  rewrite ?node_24660.
  rewrite ?node_24664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24666 (s : N.State) (i : N.Inputs) :
  R.v24666 (state s) (inputs i) = Zmod.unsigned (N.v24666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24666 s i)) at 1.
  unfold R.v24666, N.v24666.
  unfold R.v6, N.v6.
  rewrite ?node_24665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24667 (s : N.State) (i : N.Inputs) :
  R.v24667 (state s) (inputs i) = Zmod.unsigned (N.v24667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24667 s i)) at 1.
  unfold R.v24667, N.v24667.
  rewrite ?node_9237.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24668 (s : N.State) (i : N.Inputs) :
  R.v24668 (state s) (inputs i) = Zmod.unsigned (N.v24668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24668 s i)) at 1.
  unfold R.v24668, N.v24668.
  unfold R.v6, N.v6.
  rewrite ?node_9378.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24669 (s : N.State) (i : N.Inputs) :
  R.v24669 (state s) (inputs i) = Zmod.unsigned (N.v24669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24669 s i)) at 1.
  unfold R.v24669, N.v24669.
  unfold R.v6, N.v6.
  rewrite ?node_9441.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24670 (s : N.State) (i : N.Inputs) :
  R.v24670 (state s) (inputs i) = Zmod.unsigned (N.v24670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24670 s i)) at 1.
  unfold R.v24670, N.v24670.
  rewrite ?node_24667.
  rewrite ?node_24668.
  rewrite ?node_24669.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24671 (s : N.State) (i : N.Inputs) :
  R.v24671 (state s) (inputs i) = Zmod.unsigned (N.v24671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24671 s i)) at 1.
  unfold R.v24671, N.v24671.
  rewrite ?node_24666.
  rewrite ?node_24670.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24672 (s : N.State) (i : N.Inputs) :
  R.v24672 (state s) (inputs i) = Zmod.unsigned (N.v24672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24672 s i)) at 1.
  unfold R.v24672, N.v24672.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24673 (s : N.State) (i : N.Inputs) :
  R.v24673 (state s) (inputs i) = Zmod.unsigned (N.v24673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24673 s i)) at 1.
  unfold R.v24673, N.v24673.
  unfold R.v16463, N.v16463.
  rewrite !state_r900_nr_5F900.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r900_nr_5F900 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24674 (s : N.State) (i : N.Inputs) :
  R.v24674 (state s) (inputs i) = Zmod.unsigned (N.v24674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24674 s i)) at 1.
  unfold R.v24674, N.v24674.
  unfold R.v6, N.v6.
  rewrite !state_r899_nr_5F899.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r899_nr_5F899 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24675 (s : N.State) (i : N.Inputs) :
  R.v24675 (state s) (inputs i) = Zmod.unsigned (N.v24675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24675 s i)) at 1.
  unfold R.v24675, N.v24675.
  unfold R.v6, N.v6.
  rewrite !state_r898_nr_5F898.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r898_nr_5F898 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24676 (s : N.State) (i : N.Inputs) :
  R.v24676 (state s) (inputs i) = Zmod.unsigned (N.v24676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24676 s i)) at 1.
  unfold R.v24676, N.v24676.
  rewrite ?node_24674.
  rewrite ?node_24675.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24677 (s : N.State) (i : N.Inputs) :
  R.v24677 (state s) (inputs i) = Zmod.unsigned (N.v24677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24677 s i)) at 1.
  unfold R.v24677, N.v24677.
  unfold R.v16484, N.v16484.
  rewrite ?node_24676.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24678 (s : N.State) (i : N.Inputs) :
  R.v24678 (state s) (inputs i) = Zmod.unsigned (N.v24678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24678 s i)) at 1.
  unfold R.v24678, N.v24678.
  rewrite ?node_24673.
  rewrite ?node_24677.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24679 (s : N.State) (i : N.Inputs) :
  R.v24679 (state s) (inputs i) = Zmod.unsigned (N.v24679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24679 s i)) at 1.
  unfold R.v24679, N.v24679.
  unfold R.v6, N.v6.
  rewrite ?node_24678.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24680 (s : N.State) (i : N.Inputs) :
  R.v24680 (state s) (inputs i) = Zmod.unsigned (N.v24680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24680 s i)) at 1.
  unfold R.v24680, N.v24680.
  rewrite ?node_9232.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24681 (s : N.State) (i : N.Inputs) :
  R.v24681 (state s) (inputs i) = Zmod.unsigned (N.v24681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24681 s i)) at 1.
  unfold R.v24681, N.v24681.
  unfold R.v6, N.v6.
  rewrite ?node_9378.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24682 (s : N.State) (i : N.Inputs) :
  R.v24682 (state s) (inputs i) = Zmod.unsigned (N.v24682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24682 s i)) at 1.
  unfold R.v24682, N.v24682.
  rewrite ?node_24680.
  rewrite ?node_24681.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24683 (s : N.State) (i : N.Inputs) :
  R.v24683 (state s) (inputs i) = Zmod.unsigned (N.v24683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24683 s i)) at 1.
  unfold R.v24683, N.v24683.
  rewrite ?node_24679.
  rewrite ?node_24682.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24684 (s : N.State) (i : N.Inputs) :
  R.v24684 (state s) (inputs i) = Zmod.unsigned (N.v24684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24684 s i)) at 1.
  unfold R.v24684, N.v24684.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24685 (s : N.State) (i : N.Inputs) :
  R.v24685 (state s) (inputs i) = Zmod.unsigned (N.v24685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24685 s i)) at 1.
  unfold R.v24685, N.v24685.
  rewrite ?node_9236.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24686 (s : N.State) (i : N.Inputs) :
  R.v24686 (state s) (inputs i) = Zmod.unsigned (N.v24686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24686 s i)) at 1.
  unfold R.v24686, N.v24686.
  unfold R.v6, N.v6.
  rewrite !state_r901_nr_5F901.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r901_nr_5F901 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24687 (s : N.State) (i : N.Inputs) :
  R.v24687 (state s) (inputs i) = Zmod.unsigned (N.v24687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24687 s i)) at 1.
  unfold R.v24687, N.v24687.
  unfold R.v6, N.v6.
  rewrite ?node_9232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24688 (s : N.State) (i : N.Inputs) :
  R.v24688 (state s) (inputs i) = Zmod.unsigned (N.v24688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24688 s i)) at 1.
  unfold R.v24688, N.v24688.
  rewrite ?node_24686.
  rewrite ?node_24687.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24689 (s : N.State) (i : N.Inputs) :
  R.v24689 (state s) (inputs i) = Zmod.unsigned (N.v24689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24689 s i)) at 1.
  unfold R.v24689, N.v24689.
  unfold R.v16484, N.v16484.
  rewrite ?node_24688.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24690 (s : N.State) (i : N.Inputs) :
  R.v24690 (state s) (inputs i) = Zmod.unsigned (N.v24690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24690 s i)) at 1.
  unfold R.v24690, N.v24690.
  rewrite ?node_24685.
  rewrite ?node_24689.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24691 (s : N.State) (i : N.Inputs) :
  R.v24691 (state s) (inputs i) = Zmod.unsigned (N.v24691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24691 s i)) at 1.
  unfold R.v24691, N.v24691.
  unfold R.v6, N.v6.
  rewrite ?node_24690.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24692 (s : N.State) (i : N.Inputs) :
  R.v24692 (state s) (inputs i) = Zmod.unsigned (N.v24692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24692 s i)) at 1.
  unfold R.v24692, N.v24692.
  rewrite ?node_9237.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24693 (s : N.State) (i : N.Inputs) :
  R.v24693 (state s) (inputs i) = Zmod.unsigned (N.v24693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24693 s i)) at 1.
  unfold R.v24693, N.v24693.
  unfold R.v6, N.v6.
  rewrite ?node_9441.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24694 (s : N.State) (i : N.Inputs) :
  R.v24694 (state s) (inputs i) = Zmod.unsigned (N.v24694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24694 s i)) at 1.
  unfold R.v24694, N.v24694.
  rewrite ?node_24692.
  rewrite ?node_24693.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24695 (s : N.State) (i : N.Inputs) :
  R.v24695 (state s) (inputs i) = Zmod.unsigned (N.v24695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24695 s i)) at 1.
  unfold R.v24695, N.v24695.
  rewrite ?node_24691.
  rewrite ?node_24694.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24696 (s : N.State) (i : N.Inputs) :
  R.v24696 (state s) (inputs i) = Zmod.unsigned (N.v24696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24696 s i)) at 1.
  unfold R.v24696, N.v24696.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24697 (s : N.State) (i : N.Inputs) :
  R.v24697 (state s) (inputs i) = Zmod.unsigned (N.v24697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24697 s i)) at 1.
  unfold R.v24697, N.v24697.
  rewrite ?node_9243.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24698 (s : N.State) (i : N.Inputs) :
  R.v24698 (state s) (inputs i) = Zmod.unsigned (N.v24698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24698 s i)) at 1.
  unfold R.v24698, N.v24698.
  unfold R.v16463, N.v16463.
  rewrite !state_r905_nr_5F905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r905_nr_5F905 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24699 (s : N.State) (i : N.Inputs) :
  R.v24699 (state s) (inputs i) = Zmod.unsigned (N.v24699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24699 s i)) at 1.
  unfold R.v24699, N.v24699.
  unfold R.v16463, N.v16463.
  rewrite !state_r904_nr_5F904.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r904_nr_5F904 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24700 (s : N.State) (i : N.Inputs) :
  R.v24700 (state s) (inputs i) = Zmod.unsigned (N.v24700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24700 s i)) at 1.
  unfold R.v24700, N.v24700.
  unfold R.v6, N.v6.
  rewrite !state_r903_nr_5F903.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r903_nr_5F903 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24701 (s : N.State) (i : N.Inputs) :
  R.v24701 (state s) (inputs i) = Zmod.unsigned (N.v24701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24701 s i)) at 1.
  unfold R.v24701, N.v24701.
  unfold R.v6, N.v6.
  rewrite !state_r902_nr_5F902.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r902_nr_5F902 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24702 (s : N.State) (i : N.Inputs) :
  R.v24702 (state s) (inputs i) = Zmod.unsigned (N.v24702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24702 s i)) at 1.
  unfold R.v24702, N.v24702.
  rewrite ?node_24700.
  rewrite ?node_24701.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24703 (s : N.State) (i : N.Inputs) :
  R.v24703 (state s) (inputs i) = Zmod.unsigned (N.v24703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24703 s i)) at 1.
  unfold R.v24703, N.v24703.
  unfold R.v16484, N.v16484.
  rewrite ?node_24702.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24704 (s : N.State) (i : N.Inputs) :
  R.v24704 (state s) (inputs i) = Zmod.unsigned (N.v24704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24704 s i)) at 1.
  unfold R.v24704, N.v24704.
  rewrite ?node_24697.
  rewrite ?node_24698.
  rewrite ?node_24699.
  rewrite ?node_24703.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24705 (s : N.State) (i : N.Inputs) :
  R.v24705 (state s) (inputs i) = Zmod.unsigned (N.v24705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24705 s i)) at 1.
  unfold R.v24705, N.v24705.
  unfold R.v6, N.v6.
  rewrite ?node_24704.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24706 (s : N.State) (i : N.Inputs) :
  R.v24706 (state s) (inputs i) = Zmod.unsigned (N.v24706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24706 s i)) at 1.
  unfold R.v24706, N.v24706.
  rewrite ?node_9244.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24707 (s : N.State) (i : N.Inputs) :
  R.v24707 (state s) (inputs i) = Zmod.unsigned (N.v24707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24707 s i)) at 1.
  unfold R.v24707, N.v24707.
  unfold R.v6, N.v6.
  rewrite ?node_9385.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24708 (s : N.State) (i : N.Inputs) :
  R.v24708 (state s) (inputs i) = Zmod.unsigned (N.v24708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24708 s i)) at 1.
  unfold R.v24708, N.v24708.
  unfold R.v6, N.v6.
  rewrite ?node_9444.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24709 (s : N.State) (i : N.Inputs) :
  R.v24709 (state s) (inputs i) = Zmod.unsigned (N.v24709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24709 s i)) at 1.
  unfold R.v24709, N.v24709.
  rewrite ?node_24706.
  rewrite ?node_24707.
  rewrite ?node_24708.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24710 (s : N.State) (i : N.Inputs) :
  R.v24710 (state s) (inputs i) = Zmod.unsigned (N.v24710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24710 s i)) at 1.
  unfold R.v24710, N.v24710.
  rewrite ?node_24705.
  rewrite ?node_24709.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24711 (s : N.State) (i : N.Inputs) :
  R.v24711 (state s) (inputs i) = Zmod.unsigned (N.v24711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24711 s i)) at 1.
  unfold R.v24711, N.v24711.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24712 (s : N.State) (i : N.Inputs) :
  R.v24712 (state s) (inputs i) = Zmod.unsigned (N.v24712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24712 s i)) at 1.
  unfold R.v24712, N.v24712.
  unfold R.v16463, N.v16463.
  rewrite !state_r904_nr_5F904.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r904_nr_5F904 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24713 (s : N.State) (i : N.Inputs) :
  R.v24713 (state s) (inputs i) = Zmod.unsigned (N.v24713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24713 s i)) at 1.
  unfold R.v24713, N.v24713.
  unfold R.v6, N.v6.
  rewrite !state_r903_nr_5F903.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r903_nr_5F903 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24714 (s : N.State) (i : N.Inputs) :
  R.v24714 (state s) (inputs i) = Zmod.unsigned (N.v24714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24714 s i)) at 1.
  unfold R.v24714, N.v24714.
  unfold R.v6, N.v6.
  rewrite !state_r902_nr_5F902.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r902_nr_5F902 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24715 (s : N.State) (i : N.Inputs) :
  R.v24715 (state s) (inputs i) = Zmod.unsigned (N.v24715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24715 s i)) at 1.
  unfold R.v24715, N.v24715.
  rewrite ?node_24713.
  rewrite ?node_24714.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24716 (s : N.State) (i : N.Inputs) :
  R.v24716 (state s) (inputs i) = Zmod.unsigned (N.v24716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24716 s i)) at 1.
  unfold R.v24716, N.v24716.
  unfold R.v16484, N.v16484.
  rewrite ?node_24715.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24717 (s : N.State) (i : N.Inputs) :
  R.v24717 (state s) (inputs i) = Zmod.unsigned (N.v24717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24717 s i)) at 1.
  unfold R.v24717, N.v24717.
  rewrite ?node_24712.
  rewrite ?node_24716.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24718 (s : N.State) (i : N.Inputs) :
  R.v24718 (state s) (inputs i) = Zmod.unsigned (N.v24718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24718 s i)) at 1.
  unfold R.v24718, N.v24718.
  unfold R.v6, N.v6.
  rewrite ?node_24717.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24719 (s : N.State) (i : N.Inputs) :
  R.v24719 (state s) (inputs i) = Zmod.unsigned (N.v24719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24719 s i)) at 1.
  unfold R.v24719, N.v24719.
  rewrite ?node_9239.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24720 (s : N.State) (i : N.Inputs) :
  R.v24720 (state s) (inputs i) = Zmod.unsigned (N.v24720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24720 s i)) at 1.
  unfold R.v24720, N.v24720.
  unfold R.v6, N.v6.
  rewrite ?node_9385.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24721 (s : N.State) (i : N.Inputs) :
  R.v24721 (state s) (inputs i) = Zmod.unsigned (N.v24721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24721 s i)) at 1.
  unfold R.v24721, N.v24721.
  rewrite ?node_24719.
  rewrite ?node_24720.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24722 (s : N.State) (i : N.Inputs) :
  R.v24722 (state s) (inputs i) = Zmod.unsigned (N.v24722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24722 s i)) at 1.
  unfold R.v24722, N.v24722.
  rewrite ?node_24718.
  rewrite ?node_24721.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24723 (s : N.State) (i : N.Inputs) :
  R.v24723 (state s) (inputs i) = Zmod.unsigned (N.v24723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24723 s i)) at 1.
  unfold R.v24723, N.v24723.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24724 (s : N.State) (i : N.Inputs) :
  R.v24724 (state s) (inputs i) = Zmod.unsigned (N.v24724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24724 s i)) at 1.
  unfold R.v24724, N.v24724.
  rewrite ?node_9243.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24725 (s : N.State) (i : N.Inputs) :
  R.v24725 (state s) (inputs i) = Zmod.unsigned (N.v24725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24725 s i)) at 1.
  unfold R.v24725, N.v24725.
  unfold R.v6, N.v6.
  rewrite !state_r905_nr_5F905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r905_nr_5F905 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24726 (s : N.State) (i : N.Inputs) :
  R.v24726 (state s) (inputs i) = Zmod.unsigned (N.v24726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24726 s i)) at 1.
  unfold R.v24726, N.v24726.
  unfold R.v6, N.v6.
  rewrite ?node_9239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24727 (s : N.State) (i : N.Inputs) :
  R.v24727 (state s) (inputs i) = Zmod.unsigned (N.v24727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24727 s i)) at 1.
  unfold R.v24727, N.v24727.
  rewrite ?node_24725.
  rewrite ?node_24726.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24728 (s : N.State) (i : N.Inputs) :
  R.v24728 (state s) (inputs i) = Zmod.unsigned (N.v24728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24728 s i)) at 1.
  unfold R.v24728, N.v24728.
  unfold R.v16484, N.v16484.
  rewrite ?node_24727.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24729 (s : N.State) (i : N.Inputs) :
  R.v24729 (state s) (inputs i) = Zmod.unsigned (N.v24729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24729 s i)) at 1.
  unfold R.v24729, N.v24729.
  rewrite ?node_24724.
  rewrite ?node_24728.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24730 (s : N.State) (i : N.Inputs) :
  R.v24730 (state s) (inputs i) = Zmod.unsigned (N.v24730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24730 s i)) at 1.
  unfold R.v24730, N.v24730.
  unfold R.v6, N.v6.
  rewrite ?node_24729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24731 (s : N.State) (i : N.Inputs) :
  R.v24731 (state s) (inputs i) = Zmod.unsigned (N.v24731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24731 s i)) at 1.
  unfold R.v24731, N.v24731.
  rewrite ?node_9244.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24732 (s : N.State) (i : N.Inputs) :
  R.v24732 (state s) (inputs i) = Zmod.unsigned (N.v24732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24732 s i)) at 1.
  unfold R.v24732, N.v24732.
  unfold R.v6, N.v6.
  rewrite ?node_9444.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24733 (s : N.State) (i : N.Inputs) :
  R.v24733 (state s) (inputs i) = Zmod.unsigned (N.v24733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24733 s i)) at 1.
  unfold R.v24733, N.v24733.
  rewrite ?node_24731.
  rewrite ?node_24732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24734 (s : N.State) (i : N.Inputs) :
  R.v24734 (state s) (inputs i) = Zmod.unsigned (N.v24734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24734 s i)) at 1.
  unfold R.v24734, N.v24734.
  rewrite ?node_24730.
  rewrite ?node_24733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24735 (s : N.State) (i : N.Inputs) :
  R.v24735 (state s) (inputs i) = Zmod.unsigned (N.v24735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24735 s i)) at 1.
  unfold R.v24735, N.v24735.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24736 (s : N.State) (i : N.Inputs) :
  R.v24736 (state s) (inputs i) = Zmod.unsigned (N.v24736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24736 s i)) at 1.
  unfold R.v24736, N.v24736.
  rewrite ?node_9251.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24737 (s : N.State) (i : N.Inputs) :
  R.v24737 (state s) (inputs i) = Zmod.unsigned (N.v24737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24737 s i)) at 1.
  unfold R.v24737, N.v24737.
  unfold R.v16463, N.v16463.
  rewrite !state_r909_nr_5F909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r909_nr_5F909 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24738 (s : N.State) (i : N.Inputs) :
  R.v24738 (state s) (inputs i) = Zmod.unsigned (N.v24738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24738 s i)) at 1.
  unfold R.v24738, N.v24738.
  unfold R.v16463, N.v16463.
  rewrite !state_r908_nr_5F908.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r908_nr_5F908 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24739 (s : N.State) (i : N.Inputs) :
  R.v24739 (state s) (inputs i) = Zmod.unsigned (N.v24739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24739 s i)) at 1.
  unfold R.v24739, N.v24739.
  unfold R.v6, N.v6.
  rewrite !state_r907_nr_5F907.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r907_nr_5F907 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24740 (s : N.State) (i : N.Inputs) :
  R.v24740 (state s) (inputs i) = Zmod.unsigned (N.v24740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24740 s i)) at 1.
  unfold R.v24740, N.v24740.
  unfold R.v6, N.v6.
  rewrite !state_r906_nr_5F906.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r906_nr_5F906 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24741 (s : N.State) (i : N.Inputs) :
  R.v24741 (state s) (inputs i) = Zmod.unsigned (N.v24741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24741 s i)) at 1.
  unfold R.v24741, N.v24741.
  rewrite ?node_24739.
  rewrite ?node_24740.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24742 (s : N.State) (i : N.Inputs) :
  R.v24742 (state s) (inputs i) = Zmod.unsigned (N.v24742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24742 s i)) at 1.
  unfold R.v24742, N.v24742.
  unfold R.v16484, N.v16484.
  rewrite ?node_24741.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24743 (s : N.State) (i : N.Inputs) :
  R.v24743 (state s) (inputs i) = Zmod.unsigned (N.v24743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24743 s i)) at 1.
  unfold R.v24743, N.v24743.
  rewrite ?node_24736.
  rewrite ?node_24737.
  rewrite ?node_24738.
  rewrite ?node_24742.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24744 (s : N.State) (i : N.Inputs) :
  R.v24744 (state s) (inputs i) = Zmod.unsigned (N.v24744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24744 s i)) at 1.
  unfold R.v24744, N.v24744.
  unfold R.v6, N.v6.
  rewrite ?node_24743.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24745 (s : N.State) (i : N.Inputs) :
  R.v24745 (state s) (inputs i) = Zmod.unsigned (N.v24745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24745 s i)) at 1.
  unfold R.v24745, N.v24745.
  rewrite ?node_9252.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24746 (s : N.State) (i : N.Inputs) :
  R.v24746 (state s) (inputs i) = Zmod.unsigned (N.v24746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24746 s i)) at 1.
  unfold R.v24746, N.v24746.
  unfold R.v6, N.v6.
  rewrite ?node_9393.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24747 (s : N.State) (i : N.Inputs) :
  R.v24747 (state s) (inputs i) = Zmod.unsigned (N.v24747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24747 s i)) at 1.
  unfold R.v24747, N.v24747.
  unfold R.v6, N.v6.
  rewrite ?node_9448.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24748 (s : N.State) (i : N.Inputs) :
  R.v24748 (state s) (inputs i) = Zmod.unsigned (N.v24748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24748 s i)) at 1.
  unfold R.v24748, N.v24748.
  rewrite ?node_24745.
  rewrite ?node_24746.
  rewrite ?node_24747.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24749 (s : N.State) (i : N.Inputs) :
  R.v24749 (state s) (inputs i) = Zmod.unsigned (N.v24749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24749 s i)) at 1.
  unfold R.v24749, N.v24749.
  rewrite ?node_24744.
  rewrite ?node_24748.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24750 (s : N.State) (i : N.Inputs) :
  R.v24750 (state s) (inputs i) = Zmod.unsigned (N.v24750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24750 s i)) at 1.
  unfold R.v24750, N.v24750.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24751 (s : N.State) (i : N.Inputs) :
  R.v24751 (state s) (inputs i) = Zmod.unsigned (N.v24751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24751 s i)) at 1.
  unfold R.v24751, N.v24751.
  unfold R.v16463, N.v16463.
  rewrite !state_r908_nr_5F908.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r908_nr_5F908 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24752 (s : N.State) (i : N.Inputs) :
  R.v24752 (state s) (inputs i) = Zmod.unsigned (N.v24752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24752 s i)) at 1.
  unfold R.v24752, N.v24752.
  unfold R.v6, N.v6.
  rewrite !state_r907_nr_5F907.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r907_nr_5F907 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24753 (s : N.State) (i : N.Inputs) :
  R.v24753 (state s) (inputs i) = Zmod.unsigned (N.v24753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24753 s i)) at 1.
  unfold R.v24753, N.v24753.
  unfold R.v6, N.v6.
  rewrite !state_r906_nr_5F906.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r906_nr_5F906 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24754 (s : N.State) (i : N.Inputs) :
  R.v24754 (state s) (inputs i) = Zmod.unsigned (N.v24754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24754 s i)) at 1.
  unfold R.v24754, N.v24754.
  rewrite ?node_24752.
  rewrite ?node_24753.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24755 (s : N.State) (i : N.Inputs) :
  R.v24755 (state s) (inputs i) = Zmod.unsigned (N.v24755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24755 s i)) at 1.
  unfold R.v24755, N.v24755.
  unfold R.v16484, N.v16484.
  rewrite ?node_24754.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24756 (s : N.State) (i : N.Inputs) :
  R.v24756 (state s) (inputs i) = Zmod.unsigned (N.v24756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24756 s i)) at 1.
  unfold R.v24756, N.v24756.
  rewrite ?node_24751.
  rewrite ?node_24755.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24757 (s : N.State) (i : N.Inputs) :
  R.v24757 (state s) (inputs i) = Zmod.unsigned (N.v24757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24757 s i)) at 1.
  unfold R.v24757, N.v24757.
  unfold R.v6, N.v6.
  rewrite ?node_24756.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24758 (s : N.State) (i : N.Inputs) :
  R.v24758 (state s) (inputs i) = Zmod.unsigned (N.v24758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24758 s i)) at 1.
  unfold R.v24758, N.v24758.
  rewrite ?node_9247.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24759 (s : N.State) (i : N.Inputs) :
  R.v24759 (state s) (inputs i) = Zmod.unsigned (N.v24759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24759 s i)) at 1.
  unfold R.v24759, N.v24759.
  unfold R.v6, N.v6.
  rewrite ?node_9393.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24760 (s : N.State) (i : N.Inputs) :
  R.v24760 (state s) (inputs i) = Zmod.unsigned (N.v24760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24760 s i)) at 1.
  unfold R.v24760, N.v24760.
  rewrite ?node_24758.
  rewrite ?node_24759.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24761 (s : N.State) (i : N.Inputs) :
  R.v24761 (state s) (inputs i) = Zmod.unsigned (N.v24761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24761 s i)) at 1.
  unfold R.v24761, N.v24761.
  rewrite ?node_24757.
  rewrite ?node_24760.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24762 (s : N.State) (i : N.Inputs) :
  R.v24762 (state s) (inputs i) = Zmod.unsigned (N.v24762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24762 s i)) at 1.
  unfold R.v24762, N.v24762.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24763 (s : N.State) (i : N.Inputs) :
  R.v24763 (state s) (inputs i) = Zmod.unsigned (N.v24763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24763 s i)) at 1.
  unfold R.v24763, N.v24763.
  rewrite ?node_9251.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24764 (s : N.State) (i : N.Inputs) :
  R.v24764 (state s) (inputs i) = Zmod.unsigned (N.v24764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24764 s i)) at 1.
  unfold R.v24764, N.v24764.
  unfold R.v6, N.v6.
  rewrite !state_r909_nr_5F909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r909_nr_5F909 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24765 (s : N.State) (i : N.Inputs) :
  R.v24765 (state s) (inputs i) = Zmod.unsigned (N.v24765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24765 s i)) at 1.
  unfold R.v24765, N.v24765.
  unfold R.v6, N.v6.
  rewrite ?node_9247.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24766 (s : N.State) (i : N.Inputs) :
  R.v24766 (state s) (inputs i) = Zmod.unsigned (N.v24766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24766 s i)) at 1.
  unfold R.v24766, N.v24766.
  rewrite ?node_24764.
  rewrite ?node_24765.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24767 (s : N.State) (i : N.Inputs) :
  R.v24767 (state s) (inputs i) = Zmod.unsigned (N.v24767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24767 s i)) at 1.
  unfold R.v24767, N.v24767.
  unfold R.v16484, N.v16484.
  rewrite ?node_24766.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24768 (s : N.State) (i : N.Inputs) :
  R.v24768 (state s) (inputs i) = Zmod.unsigned (N.v24768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24768 s i)) at 1.
  unfold R.v24768, N.v24768.
  rewrite ?node_24763.
  rewrite ?node_24767.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24769 (s : N.State) (i : N.Inputs) :
  R.v24769 (state s) (inputs i) = Zmod.unsigned (N.v24769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24769 s i)) at 1.
  unfold R.v24769, N.v24769.
  unfold R.v6, N.v6.
  rewrite ?node_24768.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24770 (s : N.State) (i : N.Inputs) :
  R.v24770 (state s) (inputs i) = Zmod.unsigned (N.v24770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24770 s i)) at 1.
  unfold R.v24770, N.v24770.
  rewrite ?node_9252.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24771 (s : N.State) (i : N.Inputs) :
  R.v24771 (state s) (inputs i) = Zmod.unsigned (N.v24771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24771 s i)) at 1.
  unfold R.v24771, N.v24771.
  unfold R.v6, N.v6.
  rewrite ?node_9448.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24772 (s : N.State) (i : N.Inputs) :
  R.v24772 (state s) (inputs i) = Zmod.unsigned (N.v24772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24772 s i)) at 1.
  unfold R.v24772, N.v24772.
  rewrite ?node_24770.
  rewrite ?node_24771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24773 (s : N.State) (i : N.Inputs) :
  R.v24773 (state s) (inputs i) = Zmod.unsigned (N.v24773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24773 s i)) at 1.
  unfold R.v24773, N.v24773.
  rewrite ?node_24769.
  rewrite ?node_24772.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24774 (s : N.State) (i : N.Inputs) :
  R.v24774 (state s) (inputs i) = Zmod.unsigned (N.v24774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24774 s i)) at 1.
  unfold R.v24774, N.v24774.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24775 (s : N.State) (i : N.Inputs) :
  R.v24775 (state s) (inputs i) = Zmod.unsigned (N.v24775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24775 s i)) at 1.
  unfold R.v24775, N.v24775.
  rewrite ?node_9259.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24776 (s : N.State) (i : N.Inputs) :
  R.v24776 (state s) (inputs i) = Zmod.unsigned (N.v24776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24776 s i)) at 1.
  unfold R.v24776, N.v24776.
  unfold R.v16463, N.v16463.
  rewrite !state_r913_nr_5F913.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r913_nr_5F913 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24777 (s : N.State) (i : N.Inputs) :
  R.v24777 (state s) (inputs i) = Zmod.unsigned (N.v24777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24777 s i)) at 1.
  unfold R.v24777, N.v24777.
  unfold R.v16463, N.v16463.
  rewrite !state_r912_nr_5F912.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r912_nr_5F912 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24778 (s : N.State) (i : N.Inputs) :
  R.v24778 (state s) (inputs i) = Zmod.unsigned (N.v24778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24778 s i)) at 1.
  unfold R.v24778, N.v24778.
  unfold R.v6, N.v6.
  rewrite !state_r911_nr_5F911.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r911_nr_5F911 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24779 (s : N.State) (i : N.Inputs) :
  R.v24779 (state s) (inputs i) = Zmod.unsigned (N.v24779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24779 s i)) at 1.
  unfold R.v24779, N.v24779.
  unfold R.v6, N.v6.
  rewrite !state_r910_nr_5F910.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r910_nr_5F910 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24780 (s : N.State) (i : N.Inputs) :
  R.v24780 (state s) (inputs i) = Zmod.unsigned (N.v24780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24780 s i)) at 1.
  unfold R.v24780, N.v24780.
  rewrite ?node_24778.
  rewrite ?node_24779.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24781 (s : N.State) (i : N.Inputs) :
  R.v24781 (state s) (inputs i) = Zmod.unsigned (N.v24781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24781 s i)) at 1.
  unfold R.v24781, N.v24781.
  unfold R.v16484, N.v16484.
  rewrite ?node_24780.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24782 (s : N.State) (i : N.Inputs) :
  R.v24782 (state s) (inputs i) = Zmod.unsigned (N.v24782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24782 s i)) at 1.
  unfold R.v24782, N.v24782.
  rewrite ?node_24775.
  rewrite ?node_24776.
  rewrite ?node_24777.
  rewrite ?node_24781.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24783 (s : N.State) (i : N.Inputs) :
  R.v24783 (state s) (inputs i) = Zmod.unsigned (N.v24783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24783 s i)) at 1.
  unfold R.v24783, N.v24783.
  unfold R.v6, N.v6.
  rewrite ?node_24782.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24784 (s : N.State) (i : N.Inputs) :
  R.v24784 (state s) (inputs i) = Zmod.unsigned (N.v24784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24784 s i)) at 1.
  unfold R.v24784, N.v24784.
  rewrite ?node_9260.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24785 (s : N.State) (i : N.Inputs) :
  R.v24785 (state s) (inputs i) = Zmod.unsigned (N.v24785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24785 s i)) at 1.
  unfold R.v24785, N.v24785.
  unfold R.v6, N.v6.
  rewrite ?node_9401.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24786 (s : N.State) (i : N.Inputs) :
  R.v24786 (state s) (inputs i) = Zmod.unsigned (N.v24786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24786 s i)) at 1.
  unfold R.v24786, N.v24786.
  unfold R.v6, N.v6.
  rewrite ?node_9452.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24787 (s : N.State) (i : N.Inputs) :
  R.v24787 (state s) (inputs i) = Zmod.unsigned (N.v24787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24787 s i)) at 1.
  unfold R.v24787, N.v24787.
  rewrite ?node_24784.
  rewrite ?node_24785.
  rewrite ?node_24786.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24788 (s : N.State) (i : N.Inputs) :
  R.v24788 (state s) (inputs i) = Zmod.unsigned (N.v24788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24788 s i)) at 1.
  unfold R.v24788, N.v24788.
  rewrite ?node_24783.
  rewrite ?node_24787.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24789 (s : N.State) (i : N.Inputs) :
  R.v24789 (state s) (inputs i) = Zmod.unsigned (N.v24789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24789 s i)) at 1.
  unfold R.v24789, N.v24789.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24790 (s : N.State) (i : N.Inputs) :
  R.v24790 (state s) (inputs i) = Zmod.unsigned (N.v24790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24790 s i)) at 1.
  unfold R.v24790, N.v24790.
  unfold R.v16463, N.v16463.
  rewrite !state_r912_nr_5F912.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r912_nr_5F912 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24791 (s : N.State) (i : N.Inputs) :
  R.v24791 (state s) (inputs i) = Zmod.unsigned (N.v24791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24791 s i)) at 1.
  unfold R.v24791, N.v24791.
  unfold R.v6, N.v6.
  rewrite !state_r911_nr_5F911.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r911_nr_5F911 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24792 (s : N.State) (i : N.Inputs) :
  R.v24792 (state s) (inputs i) = Zmod.unsigned (N.v24792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24792 s i)) at 1.
  unfold R.v24792, N.v24792.
  unfold R.v6, N.v6.
  rewrite !state_r910_nr_5F910.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r910_nr_5F910 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24793 (s : N.State) (i : N.Inputs) :
  R.v24793 (state s) (inputs i) = Zmod.unsigned (N.v24793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24793 s i)) at 1.
  unfold R.v24793, N.v24793.
  rewrite ?node_24791.
  rewrite ?node_24792.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24794 (s : N.State) (i : N.Inputs) :
  R.v24794 (state s) (inputs i) = Zmod.unsigned (N.v24794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24794 s i)) at 1.
  unfold R.v24794, N.v24794.
  unfold R.v16484, N.v16484.
  rewrite ?node_24793.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24795 (s : N.State) (i : N.Inputs) :
  R.v24795 (state s) (inputs i) = Zmod.unsigned (N.v24795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24795 s i)) at 1.
  unfold R.v24795, N.v24795.
  rewrite ?node_24790.
  rewrite ?node_24794.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24796 (s : N.State) (i : N.Inputs) :
  R.v24796 (state s) (inputs i) = Zmod.unsigned (N.v24796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24796 s i)) at 1.
  unfold R.v24796, N.v24796.
  unfold R.v6, N.v6.
  rewrite ?node_24795.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24797 (s : N.State) (i : N.Inputs) :
  R.v24797 (state s) (inputs i) = Zmod.unsigned (N.v24797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24797 s i)) at 1.
  unfold R.v24797, N.v24797.
  rewrite ?node_9255.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24798 (s : N.State) (i : N.Inputs) :
  R.v24798 (state s) (inputs i) = Zmod.unsigned (N.v24798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24798 s i)) at 1.
  unfold R.v24798, N.v24798.
  unfold R.v6, N.v6.
  rewrite ?node_9401.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24799 (s : N.State) (i : N.Inputs) :
  R.v24799 (state s) (inputs i) = Zmod.unsigned (N.v24799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24799 s i)) at 1.
  unfold R.v24799, N.v24799.
  rewrite ?node_24797.
  rewrite ?node_24798.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24800 (s : N.State) (i : N.Inputs) :
  R.v24800 (state s) (inputs i) = Zmod.unsigned (N.v24800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24800 s i)) at 1.
  unfold R.v24800, N.v24800.
  rewrite ?node_24796.
  rewrite ?node_24799.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24801 (s : N.State) (i : N.Inputs) :
  R.v24801 (state s) (inputs i) = Zmod.unsigned (N.v24801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24801 s i)) at 1.
  unfold R.v24801, N.v24801.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24802 (s : N.State) (i : N.Inputs) :
  R.v24802 (state s) (inputs i) = Zmod.unsigned (N.v24802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24802 s i)) at 1.
  unfold R.v24802, N.v24802.
  rewrite ?node_9259.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24803 (s : N.State) (i : N.Inputs) :
  R.v24803 (state s) (inputs i) = Zmod.unsigned (N.v24803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24803 s i)) at 1.
  unfold R.v24803, N.v24803.
  unfold R.v6, N.v6.
  rewrite !state_r913_nr_5F913.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r913_nr_5F913 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24804 (s : N.State) (i : N.Inputs) :
  R.v24804 (state s) (inputs i) = Zmod.unsigned (N.v24804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24804 s i)) at 1.
  unfold R.v24804, N.v24804.
  unfold R.v6, N.v6.
  rewrite ?node_9255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24805 (s : N.State) (i : N.Inputs) :
  R.v24805 (state s) (inputs i) = Zmod.unsigned (N.v24805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24805 s i)) at 1.
  unfold R.v24805, N.v24805.
  rewrite ?node_24803.
  rewrite ?node_24804.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24806 (s : N.State) (i : N.Inputs) :
  R.v24806 (state s) (inputs i) = Zmod.unsigned (N.v24806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24806 s i)) at 1.
  unfold R.v24806, N.v24806.
  unfold R.v16484, N.v16484.
  rewrite ?node_24805.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24807 (s : N.State) (i : N.Inputs) :
  R.v24807 (state s) (inputs i) = Zmod.unsigned (N.v24807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24807 s i)) at 1.
  unfold R.v24807, N.v24807.
  rewrite ?node_24802.
  rewrite ?node_24806.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24808 (s : N.State) (i : N.Inputs) :
  R.v24808 (state s) (inputs i) = Zmod.unsigned (N.v24808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24808 s i)) at 1.
  unfold R.v24808, N.v24808.
  unfold R.v6, N.v6.
  rewrite ?node_24807.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24809 (s : N.State) (i : N.Inputs) :
  R.v24809 (state s) (inputs i) = Zmod.unsigned (N.v24809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24809 s i)) at 1.
  unfold R.v24809, N.v24809.
  rewrite ?node_9260.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24810 (s : N.State) (i : N.Inputs) :
  R.v24810 (state s) (inputs i) = Zmod.unsigned (N.v24810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24810 s i)) at 1.
  unfold R.v24810, N.v24810.
  unfold R.v6, N.v6.
  rewrite ?node_9452.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24811 (s : N.State) (i : N.Inputs) :
  R.v24811 (state s) (inputs i) = Zmod.unsigned (N.v24811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24811 s i)) at 1.
  unfold R.v24811, N.v24811.
  rewrite ?node_24809.
  rewrite ?node_24810.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24812 (s : N.State) (i : N.Inputs) :
  R.v24812 (state s) (inputs i) = Zmod.unsigned (N.v24812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24812 s i)) at 1.
  unfold R.v24812, N.v24812.
  rewrite ?node_24808.
  rewrite ?node_24811.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24813 (s : N.State) (i : N.Inputs) :
  R.v24813 (state s) (inputs i) = Zmod.unsigned (N.v24813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24813 s i)) at 1.
  unfold R.v24813, N.v24813.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24814 (s : N.State) (i : N.Inputs) :
  R.v24814 (state s) (inputs i) = Zmod.unsigned (N.v24814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24814 s i)) at 1.
  unfold R.v24814, N.v24814.
  rewrite ?node_9271.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24815 (s : N.State) (i : N.Inputs) :
  R.v24815 (state s) (inputs i) = Zmod.unsigned (N.v24815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24815 s i)) at 1.
  unfold R.v24815, N.v24815.
  unfold R.v16463, N.v16463.
  rewrite !state_r917_nr_5F917.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r917_nr_5F917 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24816 (s : N.State) (i : N.Inputs) :
  R.v24816 (state s) (inputs i) = Zmod.unsigned (N.v24816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24816 s i)) at 1.
  unfold R.v24816, N.v24816.
  unfold R.v16463, N.v16463.
  rewrite !state_r916_nr_5F916.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r916_nr_5F916 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24817 (s : N.State) (i : N.Inputs) :
  R.v24817 (state s) (inputs i) = Zmod.unsigned (N.v24817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24817 s i)) at 1.
  unfold R.v24817, N.v24817.
  unfold R.v6, N.v6.
  rewrite !state_r915_nr_5F915.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r915_nr_5F915 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24818 (s : N.State) (i : N.Inputs) :
  R.v24818 (state s) (inputs i) = Zmod.unsigned (N.v24818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24818 s i)) at 1.
  unfold R.v24818, N.v24818.
  unfold R.v6, N.v6.
  rewrite !state_r914_nr_5F914.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r914_nr_5F914 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24819 (s : N.State) (i : N.Inputs) :
  R.v24819 (state s) (inputs i) = Zmod.unsigned (N.v24819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24819 s i)) at 1.
  unfold R.v24819, N.v24819.
  rewrite ?node_24817.
  rewrite ?node_24818.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24820 (s : N.State) (i : N.Inputs) :
  R.v24820 (state s) (inputs i) = Zmod.unsigned (N.v24820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24820 s i)) at 1.
  unfold R.v24820, N.v24820.
  unfold R.v16484, N.v16484.
  rewrite ?node_24819.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24821 (s : N.State) (i : N.Inputs) :
  R.v24821 (state s) (inputs i) = Zmod.unsigned (N.v24821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24821 s i)) at 1.
  unfold R.v24821, N.v24821.
  rewrite ?node_24814.
  rewrite ?node_24815.
  rewrite ?node_24816.
  rewrite ?node_24820.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24822 (s : N.State) (i : N.Inputs) :
  R.v24822 (state s) (inputs i) = Zmod.unsigned (N.v24822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24822 s i)) at 1.
  unfold R.v24822, N.v24822.
  unfold R.v6, N.v6.
  rewrite ?node_24821.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24823 (s : N.State) (i : N.Inputs) :
  R.v24823 (state s) (inputs i) = Zmod.unsigned (N.v24823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24823 s i)) at 1.
  unfold R.v24823, N.v24823.
  rewrite ?node_9272.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24824 (s : N.State) (i : N.Inputs) :
  R.v24824 (state s) (inputs i) = Zmod.unsigned (N.v24824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24824 s i)) at 1.
  unfold R.v24824, N.v24824.
  unfold R.v6, N.v6.
  rewrite ?node_9413.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24825 (s : N.State) (i : N.Inputs) :
  R.v24825 (state s) (inputs i) = Zmod.unsigned (N.v24825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24825 s i)) at 1.
  unfold R.v24825, N.v24825.
  unfold R.v6, N.v6.
  rewrite ?node_9461.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24826 (s : N.State) (i : N.Inputs) :
  R.v24826 (state s) (inputs i) = Zmod.unsigned (N.v24826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24826 s i)) at 1.
  unfold R.v24826, N.v24826.
  rewrite ?node_24823.
  rewrite ?node_24824.
  rewrite ?node_24825.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24827 (s : N.State) (i : N.Inputs) :
  R.v24827 (state s) (inputs i) = Zmod.unsigned (N.v24827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24827 s i)) at 1.
  unfold R.v24827, N.v24827.
  rewrite ?node_24822.
  rewrite ?node_24826.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24828 (s : N.State) (i : N.Inputs) :
  R.v24828 (state s) (inputs i) = Zmod.unsigned (N.v24828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24828 s i)) at 1.
  unfold R.v24828, N.v24828.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24829 (s : N.State) (i : N.Inputs) :
  R.v24829 (state s) (inputs i) = Zmod.unsigned (N.v24829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24829 s i)) at 1.
  unfold R.v24829, N.v24829.
  unfold R.v16463, N.v16463.
  rewrite !state_r916_nr_5F916.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r916_nr_5F916 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24830 (s : N.State) (i : N.Inputs) :
  R.v24830 (state s) (inputs i) = Zmod.unsigned (N.v24830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24830 s i)) at 1.
  unfold R.v24830, N.v24830.
  unfold R.v6, N.v6.
  rewrite !state_r915_nr_5F915.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r915_nr_5F915 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24831 (s : N.State) (i : N.Inputs) :
  R.v24831 (state s) (inputs i) = Zmod.unsigned (N.v24831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24831 s i)) at 1.
  unfold R.v24831, N.v24831.
  unfold R.v6, N.v6.
  rewrite !state_r914_nr_5F914.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r914_nr_5F914 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24832 (s : N.State) (i : N.Inputs) :
  R.v24832 (state s) (inputs i) = Zmod.unsigned (N.v24832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24832 s i)) at 1.
  unfold R.v24832, N.v24832.
  rewrite ?node_24830.
  rewrite ?node_24831.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24833 (s : N.State) (i : N.Inputs) :
  R.v24833 (state s) (inputs i) = Zmod.unsigned (N.v24833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24833 s i)) at 1.
  unfold R.v24833, N.v24833.
  unfold R.v16484, N.v16484.
  rewrite ?node_24832.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24834 (s : N.State) (i : N.Inputs) :
  R.v24834 (state s) (inputs i) = Zmod.unsigned (N.v24834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24834 s i)) at 1.
  unfold R.v24834, N.v24834.
  rewrite ?node_24829.
  rewrite ?node_24833.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24835 (s : N.State) (i : N.Inputs) :
  R.v24835 (state s) (inputs i) = Zmod.unsigned (N.v24835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24835 s i)) at 1.
  unfold R.v24835, N.v24835.
  unfold R.v6, N.v6.
  rewrite ?node_24834.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24836 (s : N.State) (i : N.Inputs) :
  R.v24836 (state s) (inputs i) = Zmod.unsigned (N.v24836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24836 s i)) at 1.
  unfold R.v24836, N.v24836.
  rewrite ?node_9267.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24837 (s : N.State) (i : N.Inputs) :
  R.v24837 (state s) (inputs i) = Zmod.unsigned (N.v24837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24837 s i)) at 1.
  unfold R.v24837, N.v24837.
  unfold R.v6, N.v6.
  rewrite ?node_9413.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24838 (s : N.State) (i : N.Inputs) :
  R.v24838 (state s) (inputs i) = Zmod.unsigned (N.v24838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24838 s i)) at 1.
  unfold R.v24838, N.v24838.
  rewrite ?node_24836.
  rewrite ?node_24837.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24839 (s : N.State) (i : N.Inputs) :
  R.v24839 (state s) (inputs i) = Zmod.unsigned (N.v24839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24839 s i)) at 1.
  unfold R.v24839, N.v24839.
  rewrite ?node_24835.
  rewrite ?node_24838.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24840 (s : N.State) (i : N.Inputs) :
  R.v24840 (state s) (inputs i) = Zmod.unsigned (N.v24840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24840 s i)) at 1.
  unfold R.v24840, N.v24840.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24841 (s : N.State) (i : N.Inputs) :
  R.v24841 (state s) (inputs i) = Zmod.unsigned (N.v24841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24841 s i)) at 1.
  unfold R.v24841, N.v24841.
  rewrite ?node_9271.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24842 (s : N.State) (i : N.Inputs) :
  R.v24842 (state s) (inputs i) = Zmod.unsigned (N.v24842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24842 s i)) at 1.
  unfold R.v24842, N.v24842.
  unfold R.v6, N.v6.
  rewrite !state_r917_nr_5F917.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r917_nr_5F917 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24843 (s : N.State) (i : N.Inputs) :
  R.v24843 (state s) (inputs i) = Zmod.unsigned (N.v24843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24843 s i)) at 1.
  unfold R.v24843, N.v24843.
  unfold R.v6, N.v6.
  rewrite ?node_9267.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24844 (s : N.State) (i : N.Inputs) :
  R.v24844 (state s) (inputs i) = Zmod.unsigned (N.v24844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24844 s i)) at 1.
  unfold R.v24844, N.v24844.
  rewrite ?node_24842.
  rewrite ?node_24843.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24845 (s : N.State) (i : N.Inputs) :
  R.v24845 (state s) (inputs i) = Zmod.unsigned (N.v24845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24845 s i)) at 1.
  unfold R.v24845, N.v24845.
  unfold R.v16484, N.v16484.
  rewrite ?node_24844.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24846 (s : N.State) (i : N.Inputs) :
  R.v24846 (state s) (inputs i) = Zmod.unsigned (N.v24846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24846 s i)) at 1.
  unfold R.v24846, N.v24846.
  rewrite ?node_24841.
  rewrite ?node_24845.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24847 (s : N.State) (i : N.Inputs) :
  R.v24847 (state s) (inputs i) = Zmod.unsigned (N.v24847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24847 s i)) at 1.
  unfold R.v24847, N.v24847.
  unfold R.v6, N.v6.
  rewrite ?node_24846.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24848 (s : N.State) (i : N.Inputs) :
  R.v24848 (state s) (inputs i) = Zmod.unsigned (N.v24848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24848 s i)) at 1.
  unfold R.v24848, N.v24848.
  rewrite ?node_9272.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24849 (s : N.State) (i : N.Inputs) :
  R.v24849 (state s) (inputs i) = Zmod.unsigned (N.v24849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24849 s i)) at 1.
  unfold R.v24849, N.v24849.
  unfold R.v6, N.v6.
  rewrite ?node_9461.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24850 (s : N.State) (i : N.Inputs) :
  R.v24850 (state s) (inputs i) = Zmod.unsigned (N.v24850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24850 s i)) at 1.
  unfold R.v24850, N.v24850.
  rewrite ?node_24848.
  rewrite ?node_24849.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24851 (s : N.State) (i : N.Inputs) :
  R.v24851 (state s) (inputs i) = Zmod.unsigned (N.v24851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24851 s i)) at 1.
  unfold R.v24851, N.v24851.
  rewrite ?node_24847.
  rewrite ?node_24850.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24852 (s : N.State) (i : N.Inputs) :
  R.v24852 (state s) (inputs i) = Zmod.unsigned (N.v24852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24852 s i)) at 1.
  unfold R.v24852, N.v24852.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24853 (s : N.State) (i : N.Inputs) :
  R.v24853 (state s) (inputs i) = Zmod.unsigned (N.v24853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24853 s i)) at 1.
  unfold R.v24853, N.v24853.
  rewrite ?node_9278.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24854 (s : N.State) (i : N.Inputs) :
  R.v24854 (state s) (inputs i) = Zmod.unsigned (N.v24854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24854 s i)) at 1.
  unfold R.v24854, N.v24854.
  unfold R.v16463, N.v16463.
  rewrite !state_r921_nr_5F921.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r921_nr_5F921 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24855 (s : N.State) (i : N.Inputs) :
  R.v24855 (state s) (inputs i) = Zmod.unsigned (N.v24855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24855 s i)) at 1.
  unfold R.v24855, N.v24855.
  unfold R.v16463, N.v16463.
  rewrite !state_r920_nr_5F920.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r920_nr_5F920 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24856 (s : N.State) (i : N.Inputs) :
  R.v24856 (state s) (inputs i) = Zmod.unsigned (N.v24856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24856 s i)) at 1.
  unfold R.v24856, N.v24856.
  unfold R.v6, N.v6.
  rewrite !state_r919_nr_5F919.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r919_nr_5F919 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24857 (s : N.State) (i : N.Inputs) :
  R.v24857 (state s) (inputs i) = Zmod.unsigned (N.v24857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24857 s i)) at 1.
  unfold R.v24857, N.v24857.
  unfold R.v6, N.v6.
  rewrite !state_r918_nr_5F918.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r918_nr_5F918 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24858 (s : N.State) (i : N.Inputs) :
  R.v24858 (state s) (inputs i) = Zmod.unsigned (N.v24858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24858 s i)) at 1.
  unfold R.v24858, N.v24858.
  rewrite ?node_24856.
  rewrite ?node_24857.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24859 (s : N.State) (i : N.Inputs) :
  R.v24859 (state s) (inputs i) = Zmod.unsigned (N.v24859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24859 s i)) at 1.
  unfold R.v24859, N.v24859.
  unfold R.v16484, N.v16484.
  rewrite ?node_24858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24860 (s : N.State) (i : N.Inputs) :
  R.v24860 (state s) (inputs i) = Zmod.unsigned (N.v24860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24860 s i)) at 1.
  unfold R.v24860, N.v24860.
  rewrite ?node_24853.
  rewrite ?node_24854.
  rewrite ?node_24855.
  rewrite ?node_24859.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24861 (s : N.State) (i : N.Inputs) :
  R.v24861 (state s) (inputs i) = Zmod.unsigned (N.v24861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24861 s i)) at 1.
  unfold R.v24861, N.v24861.
  unfold R.v6, N.v6.
  rewrite ?node_24860.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24862 (s : N.State) (i : N.Inputs) :
  R.v24862 (state s) (inputs i) = Zmod.unsigned (N.v24862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24862 s i)) at 1.
  unfold R.v24862, N.v24862.
  rewrite ?node_9279.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24863 (s : N.State) (i : N.Inputs) :
  R.v24863 (state s) (inputs i) = Zmod.unsigned (N.v24863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24863 s i)) at 1.
  unfold R.v24863, N.v24863.
  unfold R.v6, N.v6.
  rewrite ?node_9420.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24864 (s : N.State) (i : N.Inputs) :
  R.v24864 (state s) (inputs i) = Zmod.unsigned (N.v24864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24864 s i)) at 1.
  unfold R.v24864, N.v24864.
  unfold R.v6, N.v6.
  rewrite ?node_9464.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24865 (s : N.State) (i : N.Inputs) :
  R.v24865 (state s) (inputs i) = Zmod.unsigned (N.v24865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24865 s i)) at 1.
  unfold R.v24865, N.v24865.
  rewrite ?node_24862.
  rewrite ?node_24863.
  rewrite ?node_24864.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24866 (s : N.State) (i : N.Inputs) :
  R.v24866 (state s) (inputs i) = Zmod.unsigned (N.v24866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24866 s i)) at 1.
  unfold R.v24866, N.v24866.
  rewrite ?node_24861.
  rewrite ?node_24865.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24867 (s : N.State) (i : N.Inputs) :
  R.v24867 (state s) (inputs i) = Zmod.unsigned (N.v24867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24867 s i)) at 1.
  unfold R.v24867, N.v24867.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24868 (s : N.State) (i : N.Inputs) :
  R.v24868 (state s) (inputs i) = Zmod.unsigned (N.v24868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24868 s i)) at 1.
  unfold R.v24868, N.v24868.
  unfold R.v16463, N.v16463.
  rewrite !state_r920_nr_5F920.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r920_nr_5F920 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24869 (s : N.State) (i : N.Inputs) :
  R.v24869 (state s) (inputs i) = Zmod.unsigned (N.v24869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24869 s i)) at 1.
  unfold R.v24869, N.v24869.
  unfold R.v6, N.v6.
  rewrite !state_r919_nr_5F919.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r919_nr_5F919 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24870 (s : N.State) (i : N.Inputs) :
  R.v24870 (state s) (inputs i) = Zmod.unsigned (N.v24870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24870 s i)) at 1.
  unfold R.v24870, N.v24870.
  unfold R.v6, N.v6.
  rewrite !state_r918_nr_5F918.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r918_nr_5F918 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24871 (s : N.State) (i : N.Inputs) :
  R.v24871 (state s) (inputs i) = Zmod.unsigned (N.v24871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24871 s i)) at 1.
  unfold R.v24871, N.v24871.
  rewrite ?node_24869.
  rewrite ?node_24870.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24872 (s : N.State) (i : N.Inputs) :
  R.v24872 (state s) (inputs i) = Zmod.unsigned (N.v24872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24872 s i)) at 1.
  unfold R.v24872, N.v24872.
  unfold R.v16484, N.v16484.
  rewrite ?node_24871.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24873 (s : N.State) (i : N.Inputs) :
  R.v24873 (state s) (inputs i) = Zmod.unsigned (N.v24873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24873 s i)) at 1.
  unfold R.v24873, N.v24873.
  rewrite ?node_24868.
  rewrite ?node_24872.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24874 (s : N.State) (i : N.Inputs) :
  R.v24874 (state s) (inputs i) = Zmod.unsigned (N.v24874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24874 s i)) at 1.
  unfold R.v24874, N.v24874.
  unfold R.v6, N.v6.
  rewrite ?node_24873.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24875 (s : N.State) (i : N.Inputs) :
  R.v24875 (state s) (inputs i) = Zmod.unsigned (N.v24875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24875 s i)) at 1.
  unfold R.v24875, N.v24875.
  rewrite ?node_9274.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24876 (s : N.State) (i : N.Inputs) :
  R.v24876 (state s) (inputs i) = Zmod.unsigned (N.v24876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24876 s i)) at 1.
  unfold R.v24876, N.v24876.
  unfold R.v6, N.v6.
  rewrite ?node_9420.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24877 (s : N.State) (i : N.Inputs) :
  R.v24877 (state s) (inputs i) = Zmod.unsigned (N.v24877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24877 s i)) at 1.
  unfold R.v24877, N.v24877.
  rewrite ?node_24875.
  rewrite ?node_24876.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24878 (s : N.State) (i : N.Inputs) :
  R.v24878 (state s) (inputs i) = Zmod.unsigned (N.v24878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24878 s i)) at 1.
  unfold R.v24878, N.v24878.
  rewrite ?node_24874.
  rewrite ?node_24877.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24879 (s : N.State) (i : N.Inputs) :
  R.v24879 (state s) (inputs i) = Zmod.unsigned (N.v24879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24879 s i)) at 1.
  unfold R.v24879, N.v24879.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24880 (s : N.State) (i : N.Inputs) :
  R.v24880 (state s) (inputs i) = Zmod.unsigned (N.v24880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24880 s i)) at 1.
  unfold R.v24880, N.v24880.
  rewrite ?node_9278.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24881 (s : N.State) (i : N.Inputs) :
  R.v24881 (state s) (inputs i) = Zmod.unsigned (N.v24881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24881 s i)) at 1.
  unfold R.v24881, N.v24881.
  unfold R.v6, N.v6.
  rewrite !state_r921_nr_5F921.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r921_nr_5F921 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24882 (s : N.State) (i : N.Inputs) :
  R.v24882 (state s) (inputs i) = Zmod.unsigned (N.v24882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24882 s i)) at 1.
  unfold R.v24882, N.v24882.
  unfold R.v6, N.v6.
  rewrite ?node_9274.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24883 (s : N.State) (i : N.Inputs) :
  R.v24883 (state s) (inputs i) = Zmod.unsigned (N.v24883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24883 s i)) at 1.
  unfold R.v24883, N.v24883.
  rewrite ?node_24881.
  rewrite ?node_24882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24884 (s : N.State) (i : N.Inputs) :
  R.v24884 (state s) (inputs i) = Zmod.unsigned (N.v24884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24884 s i)) at 1.
  unfold R.v24884, N.v24884.
  unfold R.v16484, N.v16484.
  rewrite ?node_24883.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24885 (s : N.State) (i : N.Inputs) :
  R.v24885 (state s) (inputs i) = Zmod.unsigned (N.v24885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24885 s i)) at 1.
  unfold R.v24885, N.v24885.
  rewrite ?node_24880.
  rewrite ?node_24884.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24886 (s : N.State) (i : N.Inputs) :
  R.v24886 (state s) (inputs i) = Zmod.unsigned (N.v24886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24886 s i)) at 1.
  unfold R.v24886, N.v24886.
  unfold R.v6, N.v6.
  rewrite ?node_24885.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24887 (s : N.State) (i : N.Inputs) :
  R.v24887 (state s) (inputs i) = Zmod.unsigned (N.v24887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24887 s i)) at 1.
  unfold R.v24887, N.v24887.
  rewrite ?node_9279.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24888 (s : N.State) (i : N.Inputs) :
  R.v24888 (state s) (inputs i) = Zmod.unsigned (N.v24888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24888 s i)) at 1.
  unfold R.v24888, N.v24888.
  unfold R.v6, N.v6.
  rewrite ?node_9464.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24889 (s : N.State) (i : N.Inputs) :
  R.v24889 (state s) (inputs i) = Zmod.unsigned (N.v24889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24889 s i)) at 1.
  unfold R.v24889, N.v24889.
  rewrite ?node_24887.
  rewrite ?node_24888.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24890 (s : N.State) (i : N.Inputs) :
  R.v24890 (state s) (inputs i) = Zmod.unsigned (N.v24890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24890 s i)) at 1.
  unfold R.v24890, N.v24890.
  rewrite ?node_24886.
  rewrite ?node_24889.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24891 (s : N.State) (i : N.Inputs) :
  R.v24891 (state s) (inputs i) = Zmod.unsigned (N.v24891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24891 s i)) at 1.
  unfold R.v24891, N.v24891.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24892 (s : N.State) (i : N.Inputs) :
  R.v24892 (state s) (inputs i) = Zmod.unsigned (N.v24892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24892 s i)) at 1.
  unfold R.v24892, N.v24892.
  rewrite ?node_9286.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24893 (s : N.State) (i : N.Inputs) :
  R.v24893 (state s) (inputs i) = Zmod.unsigned (N.v24893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24893 s i)) at 1.
  unfold R.v24893, N.v24893.
  unfold R.v16463, N.v16463.
  rewrite !state_r925_nr_5F925.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r925_nr_5F925 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24894 (s : N.State) (i : N.Inputs) :
  R.v24894 (state s) (inputs i) = Zmod.unsigned (N.v24894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24894 s i)) at 1.
  unfold R.v24894, N.v24894.
  unfold R.v16463, N.v16463.
  rewrite !state_r924_nr_5F924.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r924_nr_5F924 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24895 (s : N.State) (i : N.Inputs) :
  R.v24895 (state s) (inputs i) = Zmod.unsigned (N.v24895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24895 s i)) at 1.
  unfold R.v24895, N.v24895.
  unfold R.v6, N.v6.
  rewrite !state_r923_nr_5F923.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r923_nr_5F923 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24896 (s : N.State) (i : N.Inputs) :
  R.v24896 (state s) (inputs i) = Zmod.unsigned (N.v24896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24896 s i)) at 1.
  unfold R.v24896, N.v24896.
  unfold R.v6, N.v6.
  rewrite !state_r922_nr_5F922.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r922_nr_5F922 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24897 (s : N.State) (i : N.Inputs) :
  R.v24897 (state s) (inputs i) = Zmod.unsigned (N.v24897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24897 s i)) at 1.
  unfold R.v24897, N.v24897.
  rewrite ?node_24895.
  rewrite ?node_24896.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24898 (s : N.State) (i : N.Inputs) :
  R.v24898 (state s) (inputs i) = Zmod.unsigned (N.v24898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24898 s i)) at 1.
  unfold R.v24898, N.v24898.
  unfold R.v16484, N.v16484.
  rewrite ?node_24897.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24899 (s : N.State) (i : N.Inputs) :
  R.v24899 (state s) (inputs i) = Zmod.unsigned (N.v24899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24899 s i)) at 1.
  unfold R.v24899, N.v24899.
  rewrite ?node_24892.
  rewrite ?node_24893.
  rewrite ?node_24894.
  rewrite ?node_24898.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24900 (s : N.State) (i : N.Inputs) :
  R.v24900 (state s) (inputs i) = Zmod.unsigned (N.v24900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24900 s i)) at 1.
  unfold R.v24900, N.v24900.
  unfold R.v6, N.v6.
  rewrite ?node_24899.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24901 (s : N.State) (i : N.Inputs) :
  R.v24901 (state s) (inputs i) = Zmod.unsigned (N.v24901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24901 s i)) at 1.
  unfold R.v24901, N.v24901.
  rewrite ?node_9287.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24902 (s : N.State) (i : N.Inputs) :
  R.v24902 (state s) (inputs i) = Zmod.unsigned (N.v24902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24902 s i)) at 1.
  unfold R.v24902, N.v24902.
  unfold R.v6, N.v6.
  rewrite ?node_9428.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24903 (s : N.State) (i : N.Inputs) :
  R.v24903 (state s) (inputs i) = Zmod.unsigned (N.v24903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24903 s i)) at 1.
  unfold R.v24903, N.v24903.
  unfold R.v6, N.v6.
  rewrite ?node_9468.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24904 (s : N.State) (i : N.Inputs) :
  R.v24904 (state s) (inputs i) = Zmod.unsigned (N.v24904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24904 s i)) at 1.
  unfold R.v24904, N.v24904.
  rewrite ?node_24901.
  rewrite ?node_24902.
  rewrite ?node_24903.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24905 (s : N.State) (i : N.Inputs) :
  R.v24905 (state s) (inputs i) = Zmod.unsigned (N.v24905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24905 s i)) at 1.
  unfold R.v24905, N.v24905.
  rewrite ?node_24900.
  rewrite ?node_24904.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24906 (s : N.State) (i : N.Inputs) :
  R.v24906 (state s) (inputs i) = Zmod.unsigned (N.v24906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24906 s i)) at 1.
  unfold R.v24906, N.v24906.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24907 (s : N.State) (i : N.Inputs) :
  R.v24907 (state s) (inputs i) = Zmod.unsigned (N.v24907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24907 s i)) at 1.
  unfold R.v24907, N.v24907.
  unfold R.v16463, N.v16463.
  rewrite !state_r924_nr_5F924.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r924_nr_5F924 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24908 (s : N.State) (i : N.Inputs) :
  R.v24908 (state s) (inputs i) = Zmod.unsigned (N.v24908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24908 s i)) at 1.
  unfold R.v24908, N.v24908.
  unfold R.v6, N.v6.
  rewrite !state_r923_nr_5F923.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r923_nr_5F923 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24909 (s : N.State) (i : N.Inputs) :
  R.v24909 (state s) (inputs i) = Zmod.unsigned (N.v24909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24909 s i)) at 1.
  unfold R.v24909, N.v24909.
  unfold R.v6, N.v6.
  rewrite !state_r922_nr_5F922.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r922_nr_5F922 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24910 (s : N.State) (i : N.Inputs) :
  R.v24910 (state s) (inputs i) = Zmod.unsigned (N.v24910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24910 s i)) at 1.
  unfold R.v24910, N.v24910.
  rewrite ?node_24908.
  rewrite ?node_24909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24911 (s : N.State) (i : N.Inputs) :
  R.v24911 (state s) (inputs i) = Zmod.unsigned (N.v24911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24911 s i)) at 1.
  unfold R.v24911, N.v24911.
  unfold R.v16484, N.v16484.
  rewrite ?node_24910.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24912 (s : N.State) (i : N.Inputs) :
  R.v24912 (state s) (inputs i) = Zmod.unsigned (N.v24912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24912 s i)) at 1.
  unfold R.v24912, N.v24912.
  rewrite ?node_24907.
  rewrite ?node_24911.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24913 (s : N.State) (i : N.Inputs) :
  R.v24913 (state s) (inputs i) = Zmod.unsigned (N.v24913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24913 s i)) at 1.
  unfold R.v24913, N.v24913.
  unfold R.v6, N.v6.
  rewrite ?node_24912.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24914 (s : N.State) (i : N.Inputs) :
  R.v24914 (state s) (inputs i) = Zmod.unsigned (N.v24914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24914 s i)) at 1.
  unfold R.v24914, N.v24914.
  rewrite ?node_9282.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24915 (s : N.State) (i : N.Inputs) :
  R.v24915 (state s) (inputs i) = Zmod.unsigned (N.v24915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24915 s i)) at 1.
  unfold R.v24915, N.v24915.
  unfold R.v6, N.v6.
  rewrite ?node_9428.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24916 (s : N.State) (i : N.Inputs) :
  R.v24916 (state s) (inputs i) = Zmod.unsigned (N.v24916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24916 s i)) at 1.
  unfold R.v24916, N.v24916.
  rewrite ?node_24914.
  rewrite ?node_24915.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24917 (s : N.State) (i : N.Inputs) :
  R.v24917 (state s) (inputs i) = Zmod.unsigned (N.v24917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24917 s i)) at 1.
  unfold R.v24917, N.v24917.
  rewrite ?node_24913.
  rewrite ?node_24916.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24918 (s : N.State) (i : N.Inputs) :
  R.v24918 (state s) (inputs i) = Zmod.unsigned (N.v24918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24918 s i)) at 1.
  unfold R.v24918, N.v24918.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24919 (s : N.State) (i : N.Inputs) :
  R.v24919 (state s) (inputs i) = Zmod.unsigned (N.v24919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24919 s i)) at 1.
  unfold R.v24919, N.v24919.
  rewrite ?node_9286.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24920 (s : N.State) (i : N.Inputs) :
  R.v24920 (state s) (inputs i) = Zmod.unsigned (N.v24920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24920 s i)) at 1.
  unfold R.v24920, N.v24920.
  unfold R.v6, N.v6.
  rewrite !state_r925_nr_5F925.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r925_nr_5F925 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24921 (s : N.State) (i : N.Inputs) :
  R.v24921 (state s) (inputs i) = Zmod.unsigned (N.v24921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24921 s i)) at 1.
  unfold R.v24921, N.v24921.
  unfold R.v6, N.v6.
  rewrite ?node_9282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24922 (s : N.State) (i : N.Inputs) :
  R.v24922 (state s) (inputs i) = Zmod.unsigned (N.v24922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24922 s i)) at 1.
  unfold R.v24922, N.v24922.
  rewrite ?node_24920.
  rewrite ?node_24921.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24923 (s : N.State) (i : N.Inputs) :
  R.v24923 (state s) (inputs i) = Zmod.unsigned (N.v24923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24923 s i)) at 1.
  unfold R.v24923, N.v24923.
  unfold R.v16484, N.v16484.
  rewrite ?node_24922.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24924 (s : N.State) (i : N.Inputs) :
  R.v24924 (state s) (inputs i) = Zmod.unsigned (N.v24924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24924 s i)) at 1.
  unfold R.v24924, N.v24924.
  rewrite ?node_24919.
  rewrite ?node_24923.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24925 (s : N.State) (i : N.Inputs) :
  R.v24925 (state s) (inputs i) = Zmod.unsigned (N.v24925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24925 s i)) at 1.
  unfold R.v24925, N.v24925.
  unfold R.v6, N.v6.
  rewrite ?node_24924.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24926 (s : N.State) (i : N.Inputs) :
  R.v24926 (state s) (inputs i) = Zmod.unsigned (N.v24926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24926 s i)) at 1.
  unfold R.v24926, N.v24926.
  rewrite ?node_9287.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24927 (s : N.State) (i : N.Inputs) :
  R.v24927 (state s) (inputs i) = Zmod.unsigned (N.v24927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24927 s i)) at 1.
  unfold R.v24927, N.v24927.
  unfold R.v6, N.v6.
  rewrite ?node_9468.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24928 (s : N.State) (i : N.Inputs) :
  R.v24928 (state s) (inputs i) = Zmod.unsigned (N.v24928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24928 s i)) at 1.
  unfold R.v24928, N.v24928.
  rewrite ?node_24926.
  rewrite ?node_24927.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24929 (s : N.State) (i : N.Inputs) :
  R.v24929 (state s) (inputs i) = Zmod.unsigned (N.v24929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24929 s i)) at 1.
  unfold R.v24929, N.v24929.
  rewrite ?node_24925.
  rewrite ?node_24928.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24930 (s : N.State) (i : N.Inputs) :
  R.v24930 (state s) (inputs i) = Zmod.unsigned (N.v24930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24930 s i)) at 1.
  unfold R.v24930, N.v24930.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24931 (s : N.State) (i : N.Inputs) :
  R.v24931 (state s) (inputs i) = Zmod.unsigned (N.v24931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24931 s i)) at 1.
  unfold R.v24931, N.v24931.
  unfold R.v6, N.v6.
  rewrite !state_r927_nr_5F927.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r927_nr_5F927 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24932 (s : N.State) (i : N.Inputs) :
  R.v24932 (state s) (inputs i) = Zmod.unsigned (N.v24932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24932 s i)) at 1.
  unfold R.v24932, N.v24932.
  unfold R.v6, N.v6.
  rewrite !state_r926_nr_5F926.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r926_nr_5F926 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24933 (s : N.State) (i : N.Inputs) :
  R.v24933 (state s) (inputs i) = Zmod.unsigned (N.v24933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24933 s i)) at 1.
  unfold R.v24933, N.v24933.
  rewrite ?node_24931.
  rewrite ?node_24932.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24934 (s : N.State) (i : N.Inputs) :
  R.v24934 (state s) (inputs i) = Zmod.unsigned (N.v24934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24934 s i)) at 1.
  unfold R.v24934, N.v24934.
  unfold R.v16463, N.v16463.
  rewrite ?node_24933.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24935 (s : N.State) (i : N.Inputs) :
  R.v24935 (state s) (inputs i) = Zmod.unsigned (N.v24935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24935 s i)) at 1.
  unfold R.v24935, N.v24935.
  rewrite ?node_9289.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24936 (s : N.State) (i : N.Inputs) :
  R.v24936 (state s) (inputs i) = Zmod.unsigned (N.v24936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24936 s i)) at 1.
  unfold R.v24936, N.v24936.
  unfold R.v6, N.v6.
  rewrite ?node_9470.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24937 (s : N.State) (i : N.Inputs) :
  R.v24937 (state s) (inputs i) = Zmod.unsigned (N.v24937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24937 s i)) at 1.
  unfold R.v24937, N.v24937.
  rewrite ?node_24935.
  rewrite ?node_24936.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24938 (s : N.State) (i : N.Inputs) :
  R.v24938 (state s) (inputs i) = Zmod.unsigned (N.v24938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24938 s i)) at 1.
  unfold R.v24938, N.v24938.
  rewrite ?node_24934.
  rewrite ?node_24937.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24939 (s : N.State) (i : N.Inputs) :
  R.v24939 (state s) (inputs i) = Zmod.unsigned (N.v24939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24939 s i)) at 1.
  unfold R.v24939, N.v24939.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24940 (s : N.State) (i : N.Inputs) :
  R.v24940 (state s) (inputs i) = Zmod.unsigned (N.v24940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24940 s i)) at 1.
  unfold R.v24940, N.v24940.
  rewrite ?node_9378.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24941 (s : N.State) (i : N.Inputs) :
  R.v24941 (state s) (inputs i) = Zmod.unsigned (N.v24941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24941 s i)) at 1.
  unfold R.v24941, N.v24941.
  unfold R.v16463, N.v16463.
  rewrite !state_r931_nr_5F931.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r931_nr_5F931 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24942 (s : N.State) (i : N.Inputs) :
  R.v24942 (state s) (inputs i) = Zmod.unsigned (N.v24942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24942 s i)) at 1.
  unfold R.v24942, N.v24942.
  unfold R.v16463, N.v16463.
  rewrite !state_r930_nr_5F930.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r930_nr_5F930 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24943 (s : N.State) (i : N.Inputs) :
  R.v24943 (state s) (inputs i) = Zmod.unsigned (N.v24943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24943 s i)) at 1.
  unfold R.v24943, N.v24943.
  unfold R.v6, N.v6.
  rewrite !state_r929_nr_5F929.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r929_nr_5F929 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24944 (s : N.State) (i : N.Inputs) :
  R.v24944 (state s) (inputs i) = Zmod.unsigned (N.v24944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24944 s i)) at 1.
  unfold R.v24944, N.v24944.
  unfold R.v6, N.v6.
  rewrite !state_r928_nr_5F928.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r928_nr_5F928 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24945 (s : N.State) (i : N.Inputs) :
  R.v24945 (state s) (inputs i) = Zmod.unsigned (N.v24945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24945 s i)) at 1.
  unfold R.v24945, N.v24945.
  rewrite ?node_24943.
  rewrite ?node_24944.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24946 (s : N.State) (i : N.Inputs) :
  R.v24946 (state s) (inputs i) = Zmod.unsigned (N.v24946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24946 s i)) at 1.
  unfold R.v24946, N.v24946.
  unfold R.v16484, N.v16484.
  rewrite ?node_24945.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24947 (s : N.State) (i : N.Inputs) :
  R.v24947 (state s) (inputs i) = Zmod.unsigned (N.v24947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24947 s i)) at 1.
  unfold R.v24947, N.v24947.
  rewrite ?node_24940.
  rewrite ?node_24941.
  rewrite ?node_24942.
  rewrite ?node_24946.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24948 (s : N.State) (i : N.Inputs) :
  R.v24948 (state s) (inputs i) = Zmod.unsigned (N.v24948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24948 s i)) at 1.
  unfold R.v24948, N.v24948.
  unfold R.v6, N.v6.
  rewrite ?node_24947.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24949 (s : N.State) (i : N.Inputs) :
  R.v24949 (state s) (inputs i) = Zmod.unsigned (N.v24949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24949 s i)) at 1.
  unfold R.v24949, N.v24949.
  rewrite ?node_9379.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24950 (s : N.State) (i : N.Inputs) :
  R.v24950 (state s) (inputs i) = Zmod.unsigned (N.v24950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24950 s i)) at 1.
  unfold R.v24950, N.v24950.
  unfold R.v6, N.v6.
  rewrite ?node_9523.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24951 (s : N.State) (i : N.Inputs) :
  R.v24951 (state s) (inputs i) = Zmod.unsigned (N.v24951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24951 s i)) at 1.
  unfold R.v24951, N.v24951.
  unfold R.v6, N.v6.
  rewrite ?node_9586.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24952 (s : N.State) (i : N.Inputs) :
  R.v24952 (state s) (inputs i) = Zmod.unsigned (N.v24952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24952 s i)) at 1.
  unfold R.v24952, N.v24952.
  rewrite ?node_24949.
  rewrite ?node_24950.
  rewrite ?node_24951.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24953 (s : N.State) (i : N.Inputs) :
  R.v24953 (state s) (inputs i) = Zmod.unsigned (N.v24953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24953 s i)) at 1.
  unfold R.v24953, N.v24953.
  rewrite ?node_24948.
  rewrite ?node_24952.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24954 (s : N.State) (i : N.Inputs) :
  R.v24954 (state s) (inputs i) = Zmod.unsigned (N.v24954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24954 s i)) at 1.
  unfold R.v24954, N.v24954.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24955 (s : N.State) (i : N.Inputs) :
  R.v24955 (state s) (inputs i) = Zmod.unsigned (N.v24955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24955 s i)) at 1.
  unfold R.v24955, N.v24955.
  unfold R.v16463, N.v16463.
  rewrite !state_r930_nr_5F930.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r930_nr_5F930 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24956 (s : N.State) (i : N.Inputs) :
  R.v24956 (state s) (inputs i) = Zmod.unsigned (N.v24956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24956 s i)) at 1.
  unfold R.v24956, N.v24956.
  unfold R.v6, N.v6.
  rewrite !state_r929_nr_5F929.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r929_nr_5F929 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24957 (s : N.State) (i : N.Inputs) :
  R.v24957 (state s) (inputs i) = Zmod.unsigned (N.v24957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24957 s i)) at 1.
  unfold R.v24957, N.v24957.
  unfold R.v6, N.v6.
  rewrite !state_r928_nr_5F928.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r928_nr_5F928 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24958 (s : N.State) (i : N.Inputs) :
  R.v24958 (state s) (inputs i) = Zmod.unsigned (N.v24958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24958 s i)) at 1.
  unfold R.v24958, N.v24958.
  rewrite ?node_24956.
  rewrite ?node_24957.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24959 (s : N.State) (i : N.Inputs) :
  R.v24959 (state s) (inputs i) = Zmod.unsigned (N.v24959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24959 s i)) at 1.
  unfold R.v24959, N.v24959.
  unfold R.v16484, N.v16484.
  rewrite ?node_24958.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24960 (s : N.State) (i : N.Inputs) :
  R.v24960 (state s) (inputs i) = Zmod.unsigned (N.v24960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24960 s i)) at 1.
  unfold R.v24960, N.v24960.
  rewrite ?node_24955.
  rewrite ?node_24959.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24961 (s : N.State) (i : N.Inputs) :
  R.v24961 (state s) (inputs i) = Zmod.unsigned (N.v24961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24961 s i)) at 1.
  unfold R.v24961, N.v24961.
  unfold R.v6, N.v6.
  rewrite ?node_24960.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24962 (s : N.State) (i : N.Inputs) :
  R.v24962 (state s) (inputs i) = Zmod.unsigned (N.v24962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24962 s i)) at 1.
  unfold R.v24962, N.v24962.
  rewrite ?node_9374.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24963 (s : N.State) (i : N.Inputs) :
  R.v24963 (state s) (inputs i) = Zmod.unsigned (N.v24963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24963 s i)) at 1.
  unfold R.v24963, N.v24963.
  unfold R.v6, N.v6.
  rewrite ?node_9523.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24964 (s : N.State) (i : N.Inputs) :
  R.v24964 (state s) (inputs i) = Zmod.unsigned (N.v24964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24964 s i)) at 1.
  unfold R.v24964, N.v24964.
  rewrite ?node_24962.
  rewrite ?node_24963.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24965 (s : N.State) (i : N.Inputs) :
  R.v24965 (state s) (inputs i) = Zmod.unsigned (N.v24965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24965 s i)) at 1.
  unfold R.v24965, N.v24965.
  rewrite ?node_24961.
  rewrite ?node_24964.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24966 (s : N.State) (i : N.Inputs) :
  R.v24966 (state s) (inputs i) = Zmod.unsigned (N.v24966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24966 s i)) at 1.
  unfold R.v24966, N.v24966.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24967 (s : N.State) (i : N.Inputs) :
  R.v24967 (state s) (inputs i) = Zmod.unsigned (N.v24967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24967 s i)) at 1.
  unfold R.v24967, N.v24967.
  rewrite ?node_9378.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24968 (s : N.State) (i : N.Inputs) :
  R.v24968 (state s) (inputs i) = Zmod.unsigned (N.v24968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24968 s i)) at 1.
  unfold R.v24968, N.v24968.
  unfold R.v6, N.v6.
  rewrite !state_r931_nr_5F931.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r931_nr_5F931 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24969 (s : N.State) (i : N.Inputs) :
  R.v24969 (state s) (inputs i) = Zmod.unsigned (N.v24969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24969 s i)) at 1.
  unfold R.v24969, N.v24969.
  unfold R.v6, N.v6.
  rewrite ?node_9374.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24970 (s : N.State) (i : N.Inputs) :
  R.v24970 (state s) (inputs i) = Zmod.unsigned (N.v24970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24970 s i)) at 1.
  unfold R.v24970, N.v24970.
  rewrite ?node_24968.
  rewrite ?node_24969.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24971 (s : N.State) (i : N.Inputs) :
  R.v24971 (state s) (inputs i) = Zmod.unsigned (N.v24971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24971 s i)) at 1.
  unfold R.v24971, N.v24971.
  unfold R.v16484, N.v16484.
  rewrite ?node_24970.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24972 (s : N.State) (i : N.Inputs) :
  R.v24972 (state s) (inputs i) = Zmod.unsigned (N.v24972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24972 s i)) at 1.
  unfold R.v24972, N.v24972.
  rewrite ?node_24967.
  rewrite ?node_24971.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24973 (s : N.State) (i : N.Inputs) :
  R.v24973 (state s) (inputs i) = Zmod.unsigned (N.v24973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24973 s i)) at 1.
  unfold R.v24973, N.v24973.
  unfold R.v6, N.v6.
  rewrite ?node_24972.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24974 (s : N.State) (i : N.Inputs) :
  R.v24974 (state s) (inputs i) = Zmod.unsigned (N.v24974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24974 s i)) at 1.
  unfold R.v24974, N.v24974.
  rewrite ?node_9379.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24975 (s : N.State) (i : N.Inputs) :
  R.v24975 (state s) (inputs i) = Zmod.unsigned (N.v24975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24975 s i)) at 1.
  unfold R.v24975, N.v24975.
  unfold R.v6, N.v6.
  rewrite ?node_9586.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24976 (s : N.State) (i : N.Inputs) :
  R.v24976 (state s) (inputs i) = Zmod.unsigned (N.v24976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24976 s i)) at 1.
  unfold R.v24976, N.v24976.
  rewrite ?node_24974.
  rewrite ?node_24975.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24977 (s : N.State) (i : N.Inputs) :
  R.v24977 (state s) (inputs i) = Zmod.unsigned (N.v24977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24977 s i)) at 1.
  unfold R.v24977, N.v24977.
  rewrite ?node_24973.
  rewrite ?node_24976.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24978 (s : N.State) (i : N.Inputs) :
  R.v24978 (state s) (inputs i) = Zmod.unsigned (N.v24978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24978 s i)) at 1.
  unfold R.v24978, N.v24978.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24979 (s : N.State) (i : N.Inputs) :
  R.v24979 (state s) (inputs i) = Zmod.unsigned (N.v24979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24979 s i)) at 1.
  unfold R.v24979, N.v24979.
  rewrite ?node_9385.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24980 (s : N.State) (i : N.Inputs) :
  R.v24980 (state s) (inputs i) = Zmod.unsigned (N.v24980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24980 s i)) at 1.
  unfold R.v24980, N.v24980.
  unfold R.v16463, N.v16463.
  rewrite !state_r935_nr_5F935.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r935_nr_5F935 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24981 (s : N.State) (i : N.Inputs) :
  R.v24981 (state s) (inputs i) = Zmod.unsigned (N.v24981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24981 s i)) at 1.
  unfold R.v24981, N.v24981.
  unfold R.v16463, N.v16463.
  rewrite !state_r934_nr_5F934.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r934_nr_5F934 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24982 (s : N.State) (i : N.Inputs) :
  R.v24982 (state s) (inputs i) = Zmod.unsigned (N.v24982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24982 s i)) at 1.
  unfold R.v24982, N.v24982.
  unfold R.v6, N.v6.
  rewrite !state_r933_nr_5F933.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r933_nr_5F933 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24983 (s : N.State) (i : N.Inputs) :
  R.v24983 (state s) (inputs i) = Zmod.unsigned (N.v24983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24983 s i)) at 1.
  unfold R.v24983, N.v24983.
  unfold R.v6, N.v6.
  rewrite !state_r932_nr_5F932.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r932_nr_5F932 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24984 (s : N.State) (i : N.Inputs) :
  R.v24984 (state s) (inputs i) = Zmod.unsigned (N.v24984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24984 s i)) at 1.
  unfold R.v24984, N.v24984.
  rewrite ?node_24982.
  rewrite ?node_24983.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24985 (s : N.State) (i : N.Inputs) :
  R.v24985 (state s) (inputs i) = Zmod.unsigned (N.v24985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24985 s i)) at 1.
  unfold R.v24985, N.v24985.
  unfold R.v16484, N.v16484.
  rewrite ?node_24984.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24986 (s : N.State) (i : N.Inputs) :
  R.v24986 (state s) (inputs i) = Zmod.unsigned (N.v24986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24986 s i)) at 1.
  unfold R.v24986, N.v24986.
  rewrite ?node_24979.
  rewrite ?node_24980.
  rewrite ?node_24981.
  rewrite ?node_24985.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24987 (s : N.State) (i : N.Inputs) :
  R.v24987 (state s) (inputs i) = Zmod.unsigned (N.v24987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24987 s i)) at 1.
  unfold R.v24987, N.v24987.
  unfold R.v6, N.v6.
  rewrite ?node_24986.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24988 (s : N.State) (i : N.Inputs) :
  R.v24988 (state s) (inputs i) = Zmod.unsigned (N.v24988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24988 s i)) at 1.
  unfold R.v24988, N.v24988.
  rewrite ?node_9386.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24989 (s : N.State) (i : N.Inputs) :
  R.v24989 (state s) (inputs i) = Zmod.unsigned (N.v24989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24989 s i)) at 1.
  unfold R.v24989, N.v24989.
  unfold R.v6, N.v6.
  rewrite ?node_9530.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24990 (s : N.State) (i : N.Inputs) :
  R.v24990 (state s) (inputs i) = Zmod.unsigned (N.v24990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24990 s i)) at 1.
  unfold R.v24990, N.v24990.
  unfold R.v6, N.v6.
  rewrite ?node_9589.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24991 (s : N.State) (i : N.Inputs) :
  R.v24991 (state s) (inputs i) = Zmod.unsigned (N.v24991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24991 s i)) at 1.
  unfold R.v24991, N.v24991.
  rewrite ?node_24988.
  rewrite ?node_24989.
  rewrite ?node_24990.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24992 (s : N.State) (i : N.Inputs) :
  R.v24992 (state s) (inputs i) = Zmod.unsigned (N.v24992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24992 s i)) at 1.
  unfold R.v24992, N.v24992.
  rewrite ?node_24987.
  rewrite ?node_24991.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24993 (s : N.State) (i : N.Inputs) :
  R.v24993 (state s) (inputs i) = Zmod.unsigned (N.v24993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24993 s i)) at 1.
  unfold R.v24993, N.v24993.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24994 (s : N.State) (i : N.Inputs) :
  R.v24994 (state s) (inputs i) = Zmod.unsigned (N.v24994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24994 s i)) at 1.
  unfold R.v24994, N.v24994.
  unfold R.v16463, N.v16463.
  rewrite !state_r934_nr_5F934.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r934_nr_5F934 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24995 (s : N.State) (i : N.Inputs) :
  R.v24995 (state s) (inputs i) = Zmod.unsigned (N.v24995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24995 s i)) at 1.
  unfold R.v24995, N.v24995.
  unfold R.v6, N.v6.
  rewrite !state_r933_nr_5F933.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r933_nr_5F933 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24996 (s : N.State) (i : N.Inputs) :
  R.v24996 (state s) (inputs i) = Zmod.unsigned (N.v24996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24996 s i)) at 1.
  unfold R.v24996, N.v24996.
  unfold R.v6, N.v6.
  rewrite !state_r932_nr_5F932.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r932_nr_5F932 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24997 (s : N.State) (i : N.Inputs) :
  R.v24997 (state s) (inputs i) = Zmod.unsigned (N.v24997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24997 s i)) at 1.
  unfold R.v24997, N.v24997.
  rewrite ?node_24995.
  rewrite ?node_24996.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24998 (s : N.State) (i : N.Inputs) :
  R.v24998 (state s) (inputs i) = Zmod.unsigned (N.v24998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24998 s i)) at 1.
  unfold R.v24998, N.v24998.
  unfold R.v16484, N.v16484.
  rewrite ?node_24997.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_24999 (s : N.State) (i : N.Inputs) :
  R.v24999 (state s) (inputs i) = Zmod.unsigned (N.v24999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v24999 s i)) at 1.
  unfold R.v24999, N.v24999.
  rewrite ?node_24994.
  rewrite ?node_24998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
