(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes025.
Lemma node_26000 (s : N.State) (i : N.Inputs) :
  R.v26000 (state s) (inputs i) = Zmod.unsigned (N.v26000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26000 s i)) at 1.
  unfold R.v26000, N.v26000.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26001 (s : N.State) (i : N.Inputs) :
  R.v26001 (state s) (inputs i) = Zmod.unsigned (N.v26001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26001 s i)) at 1.
  unfold R.v26001, N.v26001.
  rewrite ?node_9857.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26002 (s : N.State) (i : N.Inputs) :
  R.v26002 (state s) (inputs i) = Zmod.unsigned (N.v26002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26002 s i)) at 1.
  unfold R.v26002, N.v26002.
  unfold R.v6, N.v6.
  rewrite !state_r1041_nr_5F1041.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1041_nr_5F1041 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26003 (s : N.State) (i : N.Inputs) :
  R.v26003 (state s) (inputs i) = Zmod.unsigned (N.v26003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26003 s i)) at 1.
  unfold R.v26003, N.v26003.
  unfold R.v6, N.v6.
  rewrite ?node_9853.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26004 (s : N.State) (i : N.Inputs) :
  R.v26004 (state s) (inputs i) = Zmod.unsigned (N.v26004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26004 s i)) at 1.
  unfold R.v26004, N.v26004.
  rewrite ?node_26002.
  rewrite ?node_26003.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26005 (s : N.State) (i : N.Inputs) :
  R.v26005 (state s) (inputs i) = Zmod.unsigned (N.v26005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26005 s i)) at 1.
  unfold R.v26005, N.v26005.
  unfold R.v16484, N.v16484.
  rewrite ?node_26004.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26006 (s : N.State) (i : N.Inputs) :
  R.v26006 (state s) (inputs i) = Zmod.unsigned (N.v26006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26006 s i)) at 1.
  unfold R.v26006, N.v26006.
  rewrite ?node_26001.
  rewrite ?node_26005.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26007 (s : N.State) (i : N.Inputs) :
  R.v26007 (state s) (inputs i) = Zmod.unsigned (N.v26007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26007 s i)) at 1.
  unfold R.v26007, N.v26007.
  unfold R.v6, N.v6.
  rewrite ?node_26006.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26008 (s : N.State) (i : N.Inputs) :
  R.v26008 (state s) (inputs i) = Zmod.unsigned (N.v26008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26008 s i)) at 1.
  unfold R.v26008, N.v26008.
  rewrite ?node_9858.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26009 (s : N.State) (i : N.Inputs) :
  R.v26009 (state s) (inputs i) = Zmod.unsigned (N.v26009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26009 s i)) at 1.
  unfold R.v26009, N.v26009.
  unfold R.v6, N.v6.
  rewrite ?node_10062.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26010 (s : N.State) (i : N.Inputs) :
  R.v26010 (state s) (inputs i) = Zmod.unsigned (N.v26010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26010 s i)) at 1.
  unfold R.v26010, N.v26010.
  rewrite ?node_26008.
  rewrite ?node_26009.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26011 (s : N.State) (i : N.Inputs) :
  R.v26011 (state s) (inputs i) = Zmod.unsigned (N.v26011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26011 s i)) at 1.
  unfold R.v26011, N.v26011.
  rewrite ?node_26007.
  rewrite ?node_26010.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26012 (s : N.State) (i : N.Inputs) :
  R.v26012 (state s) (inputs i) = Zmod.unsigned (N.v26012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26012 s i)) at 1.
  unfold R.v26012, N.v26012.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26013 (s : N.State) (i : N.Inputs) :
  R.v26013 (state s) (inputs i) = Zmod.unsigned (N.v26013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26013 s i)) at 1.
  unfold R.v26013, N.v26013.
  rewrite ?node_9864.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26014 (s : N.State) (i : N.Inputs) :
  R.v26014 (state s) (inputs i) = Zmod.unsigned (N.v26014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26014 s i)) at 1.
  unfold R.v26014, N.v26014.
  unfold R.v16463, N.v16463.
  rewrite !state_r1045_nr_5F1045.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1045_nr_5F1045 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26015 (s : N.State) (i : N.Inputs) :
  R.v26015 (state s) (inputs i) = Zmod.unsigned (N.v26015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26015 s i)) at 1.
  unfold R.v26015, N.v26015.
  unfold R.v16463, N.v16463.
  rewrite !state_r1044_nr_5F1044.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1044_nr_5F1044 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26016 (s : N.State) (i : N.Inputs) :
  R.v26016 (state s) (inputs i) = Zmod.unsigned (N.v26016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26016 s i)) at 1.
  unfold R.v26016, N.v26016.
  unfold R.v6, N.v6.
  rewrite !state_r1043_nr_5F1043.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1043_nr_5F1043 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26017 (s : N.State) (i : N.Inputs) :
  R.v26017 (state s) (inputs i) = Zmod.unsigned (N.v26017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26017 s i)) at 1.
  unfold R.v26017, N.v26017.
  unfold R.v6, N.v6.
  rewrite !state_r1042_nr_5F1042.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1042_nr_5F1042 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26018 (s : N.State) (i : N.Inputs) :
  R.v26018 (state s) (inputs i) = Zmod.unsigned (N.v26018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26018 s i)) at 1.
  unfold R.v26018, N.v26018.
  rewrite ?node_26016.
  rewrite ?node_26017.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26019 (s : N.State) (i : N.Inputs) :
  R.v26019 (state s) (inputs i) = Zmod.unsigned (N.v26019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26019 s i)) at 1.
  unfold R.v26019, N.v26019.
  unfold R.v16484, N.v16484.
  rewrite ?node_26018.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26020 (s : N.State) (i : N.Inputs) :
  R.v26020 (state s) (inputs i) = Zmod.unsigned (N.v26020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26020 s i)) at 1.
  unfold R.v26020, N.v26020.
  rewrite ?node_26013.
  rewrite ?node_26014.
  rewrite ?node_26015.
  rewrite ?node_26019.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26021 (s : N.State) (i : N.Inputs) :
  R.v26021 (state s) (inputs i) = Zmod.unsigned (N.v26021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26021 s i)) at 1.
  unfold R.v26021, N.v26021.
  unfold R.v6, N.v6.
  rewrite ?node_26020.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26022 (s : N.State) (i : N.Inputs) :
  R.v26022 (state s) (inputs i) = Zmod.unsigned (N.v26022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26022 s i)) at 1.
  unfold R.v26022, N.v26022.
  rewrite ?node_9865.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26023 (s : N.State) (i : N.Inputs) :
  R.v26023 (state s) (inputs i) = Zmod.unsigned (N.v26023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26023 s i)) at 1.
  unfold R.v26023, N.v26023.
  unfold R.v6, N.v6.
  rewrite ?node_10016.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26024 (s : N.State) (i : N.Inputs) :
  R.v26024 (state s) (inputs i) = Zmod.unsigned (N.v26024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26024 s i)) at 1.
  unfold R.v26024, N.v26024.
  unfold R.v6, N.v6.
  rewrite ?node_10066.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26025 (s : N.State) (i : N.Inputs) :
  R.v26025 (state s) (inputs i) = Zmod.unsigned (N.v26025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26025 s i)) at 1.
  unfold R.v26025, N.v26025.
  rewrite ?node_26022.
  rewrite ?node_26023.
  rewrite ?node_26024.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26026 (s : N.State) (i : N.Inputs) :
  R.v26026 (state s) (inputs i) = Zmod.unsigned (N.v26026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26026 s i)) at 1.
  unfold R.v26026, N.v26026.
  rewrite ?node_26021.
  rewrite ?node_26025.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26027 (s : N.State) (i : N.Inputs) :
  R.v26027 (state s) (inputs i) = Zmod.unsigned (N.v26027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26027 s i)) at 1.
  unfold R.v26027, N.v26027.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26028 (s : N.State) (i : N.Inputs) :
  R.v26028 (state s) (inputs i) = Zmod.unsigned (N.v26028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26028 s i)) at 1.
  unfold R.v26028, N.v26028.
  unfold R.v16463, N.v16463.
  rewrite !state_r1044_nr_5F1044.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1044_nr_5F1044 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26029 (s : N.State) (i : N.Inputs) :
  R.v26029 (state s) (inputs i) = Zmod.unsigned (N.v26029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26029 s i)) at 1.
  unfold R.v26029, N.v26029.
  unfold R.v6, N.v6.
  rewrite !state_r1043_nr_5F1043.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1043_nr_5F1043 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26030 (s : N.State) (i : N.Inputs) :
  R.v26030 (state s) (inputs i) = Zmod.unsigned (N.v26030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26030 s i)) at 1.
  unfold R.v26030, N.v26030.
  unfold R.v6, N.v6.
  rewrite !state_r1042_nr_5F1042.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1042_nr_5F1042 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26031 (s : N.State) (i : N.Inputs) :
  R.v26031 (state s) (inputs i) = Zmod.unsigned (N.v26031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26031 s i)) at 1.
  unfold R.v26031, N.v26031.
  rewrite ?node_26029.
  rewrite ?node_26030.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26032 (s : N.State) (i : N.Inputs) :
  R.v26032 (state s) (inputs i) = Zmod.unsigned (N.v26032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26032 s i)) at 1.
  unfold R.v26032, N.v26032.
  unfold R.v16484, N.v16484.
  rewrite ?node_26031.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26033 (s : N.State) (i : N.Inputs) :
  R.v26033 (state s) (inputs i) = Zmod.unsigned (N.v26033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26033 s i)) at 1.
  unfold R.v26033, N.v26033.
  rewrite ?node_26028.
  rewrite ?node_26032.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26034 (s : N.State) (i : N.Inputs) :
  R.v26034 (state s) (inputs i) = Zmod.unsigned (N.v26034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26034 s i)) at 1.
  unfold R.v26034, N.v26034.
  unfold R.v6, N.v6.
  rewrite ?node_26033.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26035 (s : N.State) (i : N.Inputs) :
  R.v26035 (state s) (inputs i) = Zmod.unsigned (N.v26035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26035 s i)) at 1.
  unfold R.v26035, N.v26035.
  rewrite ?node_9860.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26036 (s : N.State) (i : N.Inputs) :
  R.v26036 (state s) (inputs i) = Zmod.unsigned (N.v26036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26036 s i)) at 1.
  unfold R.v26036, N.v26036.
  unfold R.v6, N.v6.
  rewrite ?node_10016.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26037 (s : N.State) (i : N.Inputs) :
  R.v26037 (state s) (inputs i) = Zmod.unsigned (N.v26037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26037 s i)) at 1.
  unfold R.v26037, N.v26037.
  rewrite ?node_26035.
  rewrite ?node_26036.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26038 (s : N.State) (i : N.Inputs) :
  R.v26038 (state s) (inputs i) = Zmod.unsigned (N.v26038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26038 s i)) at 1.
  unfold R.v26038, N.v26038.
  rewrite ?node_26034.
  rewrite ?node_26037.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26039 (s : N.State) (i : N.Inputs) :
  R.v26039 (state s) (inputs i) = Zmod.unsigned (N.v26039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26039 s i)) at 1.
  unfold R.v26039, N.v26039.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26040 (s : N.State) (i : N.Inputs) :
  R.v26040 (state s) (inputs i) = Zmod.unsigned (N.v26040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26040 s i)) at 1.
  unfold R.v26040, N.v26040.
  rewrite ?node_9864.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26041 (s : N.State) (i : N.Inputs) :
  R.v26041 (state s) (inputs i) = Zmod.unsigned (N.v26041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26041 s i)) at 1.
  unfold R.v26041, N.v26041.
  unfold R.v6, N.v6.
  rewrite !state_r1045_nr_5F1045.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1045_nr_5F1045 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26042 (s : N.State) (i : N.Inputs) :
  R.v26042 (state s) (inputs i) = Zmod.unsigned (N.v26042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26042 s i)) at 1.
  unfold R.v26042, N.v26042.
  unfold R.v6, N.v6.
  rewrite ?node_9860.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26043 (s : N.State) (i : N.Inputs) :
  R.v26043 (state s) (inputs i) = Zmod.unsigned (N.v26043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26043 s i)) at 1.
  unfold R.v26043, N.v26043.
  rewrite ?node_26041.
  rewrite ?node_26042.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26044 (s : N.State) (i : N.Inputs) :
  R.v26044 (state s) (inputs i) = Zmod.unsigned (N.v26044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26044 s i)) at 1.
  unfold R.v26044, N.v26044.
  unfold R.v16484, N.v16484.
  rewrite ?node_26043.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26045 (s : N.State) (i : N.Inputs) :
  R.v26045 (state s) (inputs i) = Zmod.unsigned (N.v26045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26045 s i)) at 1.
  unfold R.v26045, N.v26045.
  rewrite ?node_26040.
  rewrite ?node_26044.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26046 (s : N.State) (i : N.Inputs) :
  R.v26046 (state s) (inputs i) = Zmod.unsigned (N.v26046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26046 s i)) at 1.
  unfold R.v26046, N.v26046.
  unfold R.v6, N.v6.
  rewrite ?node_26045.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26047 (s : N.State) (i : N.Inputs) :
  R.v26047 (state s) (inputs i) = Zmod.unsigned (N.v26047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26047 s i)) at 1.
  unfold R.v26047, N.v26047.
  rewrite ?node_9865.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26048 (s : N.State) (i : N.Inputs) :
  R.v26048 (state s) (inputs i) = Zmod.unsigned (N.v26048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26048 s i)) at 1.
  unfold R.v26048, N.v26048.
  unfold R.v6, N.v6.
  rewrite ?node_10066.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26049 (s : N.State) (i : N.Inputs) :
  R.v26049 (state s) (inputs i) = Zmod.unsigned (N.v26049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26049 s i)) at 1.
  unfold R.v26049, N.v26049.
  rewrite ?node_26047.
  rewrite ?node_26048.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26050 (s : N.State) (i : N.Inputs) :
  R.v26050 (state s) (inputs i) = Zmod.unsigned (N.v26050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26050 s i)) at 1.
  unfold R.v26050, N.v26050.
  rewrite ?node_26046.
  rewrite ?node_26049.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26051 (s : N.State) (i : N.Inputs) :
  R.v26051 (state s) (inputs i) = Zmod.unsigned (N.v26051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26051 s i)) at 1.
  unfold R.v26051, N.v26051.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26052 (s : N.State) (i : N.Inputs) :
  R.v26052 (state s) (inputs i) = Zmod.unsigned (N.v26052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26052 s i)) at 1.
  unfold R.v26052, N.v26052.
  rewrite ?node_9872.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26053 (s : N.State) (i : N.Inputs) :
  R.v26053 (state s) (inputs i) = Zmod.unsigned (N.v26053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26053 s i)) at 1.
  unfold R.v26053, N.v26053.
  unfold R.v16463, N.v16463.
  rewrite !state_r1049_nr_5F1049.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1049_nr_5F1049 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26054 (s : N.State) (i : N.Inputs) :
  R.v26054 (state s) (inputs i) = Zmod.unsigned (N.v26054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26054 s i)) at 1.
  unfold R.v26054, N.v26054.
  unfold R.v16463, N.v16463.
  rewrite !state_r1048_nr_5F1048.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1048_nr_5F1048 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26055 (s : N.State) (i : N.Inputs) :
  R.v26055 (state s) (inputs i) = Zmod.unsigned (N.v26055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26055 s i)) at 1.
  unfold R.v26055, N.v26055.
  unfold R.v6, N.v6.
  rewrite !state_r1047_nr_5F1047.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1047_nr_5F1047 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26056 (s : N.State) (i : N.Inputs) :
  R.v26056 (state s) (inputs i) = Zmod.unsigned (N.v26056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26056 s i)) at 1.
  unfold R.v26056, N.v26056.
  unfold R.v6, N.v6.
  rewrite !state_r1046_nr_5F1046.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1046_nr_5F1046 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26057 (s : N.State) (i : N.Inputs) :
  R.v26057 (state s) (inputs i) = Zmod.unsigned (N.v26057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26057 s i)) at 1.
  unfold R.v26057, N.v26057.
  rewrite ?node_26055.
  rewrite ?node_26056.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26058 (s : N.State) (i : N.Inputs) :
  R.v26058 (state s) (inputs i) = Zmod.unsigned (N.v26058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26058 s i)) at 1.
  unfold R.v26058, N.v26058.
  unfold R.v16484, N.v16484.
  rewrite ?node_26057.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26059 (s : N.State) (i : N.Inputs) :
  R.v26059 (state s) (inputs i) = Zmod.unsigned (N.v26059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26059 s i)) at 1.
  unfold R.v26059, N.v26059.
  rewrite ?node_26052.
  rewrite ?node_26053.
  rewrite ?node_26054.
  rewrite ?node_26058.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26060 (s : N.State) (i : N.Inputs) :
  R.v26060 (state s) (inputs i) = Zmod.unsigned (N.v26060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26060 s i)) at 1.
  unfold R.v26060, N.v26060.
  unfold R.v6, N.v6.
  rewrite ?node_26059.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26061 (s : N.State) (i : N.Inputs) :
  R.v26061 (state s) (inputs i) = Zmod.unsigned (N.v26061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26061 s i)) at 1.
  unfold R.v26061, N.v26061.
  rewrite ?node_9873.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26062 (s : N.State) (i : N.Inputs) :
  R.v26062 (state s) (inputs i) = Zmod.unsigned (N.v26062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26062 s i)) at 1.
  unfold R.v26062, N.v26062.
  unfold R.v6, N.v6.
  rewrite ?node_10024.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26063 (s : N.State) (i : N.Inputs) :
  R.v26063 (state s) (inputs i) = Zmod.unsigned (N.v26063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26063 s i)) at 1.
  unfold R.v26063, N.v26063.
  unfold R.v6, N.v6.
  rewrite ?node_10070.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26064 (s : N.State) (i : N.Inputs) :
  R.v26064 (state s) (inputs i) = Zmod.unsigned (N.v26064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26064 s i)) at 1.
  unfold R.v26064, N.v26064.
  rewrite ?node_26061.
  rewrite ?node_26062.
  rewrite ?node_26063.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26065 (s : N.State) (i : N.Inputs) :
  R.v26065 (state s) (inputs i) = Zmod.unsigned (N.v26065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26065 s i)) at 1.
  unfold R.v26065, N.v26065.
  rewrite ?node_26060.
  rewrite ?node_26064.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26066 (s : N.State) (i : N.Inputs) :
  R.v26066 (state s) (inputs i) = Zmod.unsigned (N.v26066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26066 s i)) at 1.
  unfold R.v26066, N.v26066.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26067 (s : N.State) (i : N.Inputs) :
  R.v26067 (state s) (inputs i) = Zmod.unsigned (N.v26067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26067 s i)) at 1.
  unfold R.v26067, N.v26067.
  unfold R.v16463, N.v16463.
  rewrite !state_r1048_nr_5F1048.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1048_nr_5F1048 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26068 (s : N.State) (i : N.Inputs) :
  R.v26068 (state s) (inputs i) = Zmod.unsigned (N.v26068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26068 s i)) at 1.
  unfold R.v26068, N.v26068.
  unfold R.v6, N.v6.
  rewrite !state_r1047_nr_5F1047.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1047_nr_5F1047 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26069 (s : N.State) (i : N.Inputs) :
  R.v26069 (state s) (inputs i) = Zmod.unsigned (N.v26069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26069 s i)) at 1.
  unfold R.v26069, N.v26069.
  unfold R.v6, N.v6.
  rewrite !state_r1046_nr_5F1046.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1046_nr_5F1046 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26070 (s : N.State) (i : N.Inputs) :
  R.v26070 (state s) (inputs i) = Zmod.unsigned (N.v26070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26070 s i)) at 1.
  unfold R.v26070, N.v26070.
  rewrite ?node_26068.
  rewrite ?node_26069.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26071 (s : N.State) (i : N.Inputs) :
  R.v26071 (state s) (inputs i) = Zmod.unsigned (N.v26071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26071 s i)) at 1.
  unfold R.v26071, N.v26071.
  unfold R.v16484, N.v16484.
  rewrite ?node_26070.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26072 (s : N.State) (i : N.Inputs) :
  R.v26072 (state s) (inputs i) = Zmod.unsigned (N.v26072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26072 s i)) at 1.
  unfold R.v26072, N.v26072.
  rewrite ?node_26067.
  rewrite ?node_26071.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26073 (s : N.State) (i : N.Inputs) :
  R.v26073 (state s) (inputs i) = Zmod.unsigned (N.v26073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26073 s i)) at 1.
  unfold R.v26073, N.v26073.
  unfold R.v6, N.v6.
  rewrite ?node_26072.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26074 (s : N.State) (i : N.Inputs) :
  R.v26074 (state s) (inputs i) = Zmod.unsigned (N.v26074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26074 s i)) at 1.
  unfold R.v26074, N.v26074.
  rewrite ?node_9868.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26075 (s : N.State) (i : N.Inputs) :
  R.v26075 (state s) (inputs i) = Zmod.unsigned (N.v26075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26075 s i)) at 1.
  unfold R.v26075, N.v26075.
  unfold R.v6, N.v6.
  rewrite ?node_10024.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26076 (s : N.State) (i : N.Inputs) :
  R.v26076 (state s) (inputs i) = Zmod.unsigned (N.v26076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26076 s i)) at 1.
  unfold R.v26076, N.v26076.
  rewrite ?node_26074.
  rewrite ?node_26075.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26077 (s : N.State) (i : N.Inputs) :
  R.v26077 (state s) (inputs i) = Zmod.unsigned (N.v26077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26077 s i)) at 1.
  unfold R.v26077, N.v26077.
  rewrite ?node_26073.
  rewrite ?node_26076.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26078 (s : N.State) (i : N.Inputs) :
  R.v26078 (state s) (inputs i) = Zmod.unsigned (N.v26078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26078 s i)) at 1.
  unfold R.v26078, N.v26078.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26079 (s : N.State) (i : N.Inputs) :
  R.v26079 (state s) (inputs i) = Zmod.unsigned (N.v26079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26079 s i)) at 1.
  unfold R.v26079, N.v26079.
  rewrite ?node_9872.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26080 (s : N.State) (i : N.Inputs) :
  R.v26080 (state s) (inputs i) = Zmod.unsigned (N.v26080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26080 s i)) at 1.
  unfold R.v26080, N.v26080.
  unfold R.v6, N.v6.
  rewrite !state_r1049_nr_5F1049.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1049_nr_5F1049 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26081 (s : N.State) (i : N.Inputs) :
  R.v26081 (state s) (inputs i) = Zmod.unsigned (N.v26081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26081 s i)) at 1.
  unfold R.v26081, N.v26081.
  unfold R.v6, N.v6.
  rewrite ?node_9868.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26082 (s : N.State) (i : N.Inputs) :
  R.v26082 (state s) (inputs i) = Zmod.unsigned (N.v26082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26082 s i)) at 1.
  unfold R.v26082, N.v26082.
  rewrite ?node_26080.
  rewrite ?node_26081.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26083 (s : N.State) (i : N.Inputs) :
  R.v26083 (state s) (inputs i) = Zmod.unsigned (N.v26083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26083 s i)) at 1.
  unfold R.v26083, N.v26083.
  unfold R.v16484, N.v16484.
  rewrite ?node_26082.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26084 (s : N.State) (i : N.Inputs) :
  R.v26084 (state s) (inputs i) = Zmod.unsigned (N.v26084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26084 s i)) at 1.
  unfold R.v26084, N.v26084.
  rewrite ?node_26079.
  rewrite ?node_26083.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26085 (s : N.State) (i : N.Inputs) :
  R.v26085 (state s) (inputs i) = Zmod.unsigned (N.v26085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26085 s i)) at 1.
  unfold R.v26085, N.v26085.
  unfold R.v6, N.v6.
  rewrite ?node_26084.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26086 (s : N.State) (i : N.Inputs) :
  R.v26086 (state s) (inputs i) = Zmod.unsigned (N.v26086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26086 s i)) at 1.
  unfold R.v26086, N.v26086.
  rewrite ?node_9873.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26087 (s : N.State) (i : N.Inputs) :
  R.v26087 (state s) (inputs i) = Zmod.unsigned (N.v26087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26087 s i)) at 1.
  unfold R.v26087, N.v26087.
  unfold R.v6, N.v6.
  rewrite ?node_10070.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26088 (s : N.State) (i : N.Inputs) :
  R.v26088 (state s) (inputs i) = Zmod.unsigned (N.v26088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26088 s i)) at 1.
  unfold R.v26088, N.v26088.
  rewrite ?node_26086.
  rewrite ?node_26087.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26089 (s : N.State) (i : N.Inputs) :
  R.v26089 (state s) (inputs i) = Zmod.unsigned (N.v26089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26089 s i)) at 1.
  unfold R.v26089, N.v26089.
  rewrite ?node_26085.
  rewrite ?node_26088.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26090 (s : N.State) (i : N.Inputs) :
  R.v26090 (state s) (inputs i) = Zmod.unsigned (N.v26090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26090 s i)) at 1.
  unfold R.v26090, N.v26090.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26091 (s : N.State) (i : N.Inputs) :
  R.v26091 (state s) (inputs i) = Zmod.unsigned (N.v26091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26091 s i)) at 1.
  unfold R.v26091, N.v26091.
  rewrite ?node_9880.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26092 (s : N.State) (i : N.Inputs) :
  R.v26092 (state s) (inputs i) = Zmod.unsigned (N.v26092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26092 s i)) at 1.
  unfold R.v26092, N.v26092.
  unfold R.v16463, N.v16463.
  rewrite !state_r1053_nr_5F1053.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1053_nr_5F1053 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26093 (s : N.State) (i : N.Inputs) :
  R.v26093 (state s) (inputs i) = Zmod.unsigned (N.v26093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26093 s i)) at 1.
  unfold R.v26093, N.v26093.
  unfold R.v16463, N.v16463.
  rewrite !state_r1052_nr_5F1052.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1052_nr_5F1052 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26094 (s : N.State) (i : N.Inputs) :
  R.v26094 (state s) (inputs i) = Zmod.unsigned (N.v26094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26094 s i)) at 1.
  unfold R.v26094, N.v26094.
  unfold R.v6, N.v6.
  rewrite !state_r1051_nr_5F1051.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1051_nr_5F1051 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26095 (s : N.State) (i : N.Inputs) :
  R.v26095 (state s) (inputs i) = Zmod.unsigned (N.v26095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26095 s i)) at 1.
  unfold R.v26095, N.v26095.
  unfold R.v6, N.v6.
  rewrite !state_r1050_nr_5F1050.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1050_nr_5F1050 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26096 (s : N.State) (i : N.Inputs) :
  R.v26096 (state s) (inputs i) = Zmod.unsigned (N.v26096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26096 s i)) at 1.
  unfold R.v26096, N.v26096.
  rewrite ?node_26094.
  rewrite ?node_26095.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26097 (s : N.State) (i : N.Inputs) :
  R.v26097 (state s) (inputs i) = Zmod.unsigned (N.v26097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26097 s i)) at 1.
  unfold R.v26097, N.v26097.
  unfold R.v16484, N.v16484.
  rewrite ?node_26096.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26098 (s : N.State) (i : N.Inputs) :
  R.v26098 (state s) (inputs i) = Zmod.unsigned (N.v26098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26098 s i)) at 1.
  unfold R.v26098, N.v26098.
  rewrite ?node_26091.
  rewrite ?node_26092.
  rewrite ?node_26093.
  rewrite ?node_26097.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26099 (s : N.State) (i : N.Inputs) :
  R.v26099 (state s) (inputs i) = Zmod.unsigned (N.v26099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26099 s i)) at 1.
  unfold R.v26099, N.v26099.
  unfold R.v6, N.v6.
  rewrite ?node_26098.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26100 (s : N.State) (i : N.Inputs) :
  R.v26100 (state s) (inputs i) = Zmod.unsigned (N.v26100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26100 s i)) at 1.
  unfold R.v26100, N.v26100.
  rewrite ?node_9881.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26101 (s : N.State) (i : N.Inputs) :
  R.v26101 (state s) (inputs i) = Zmod.unsigned (N.v26101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26101 s i)) at 1.
  unfold R.v26101, N.v26101.
  unfold R.v6, N.v6.
  rewrite ?node_10032.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26102 (s : N.State) (i : N.Inputs) :
  R.v26102 (state s) (inputs i) = Zmod.unsigned (N.v26102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26102 s i)) at 1.
  unfold R.v26102, N.v26102.
  unfold R.v6, N.v6.
  rewrite ?node_10083.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26103 (s : N.State) (i : N.Inputs) :
  R.v26103 (state s) (inputs i) = Zmod.unsigned (N.v26103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26103 s i)) at 1.
  unfold R.v26103, N.v26103.
  rewrite ?node_26100.
  rewrite ?node_26101.
  rewrite ?node_26102.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26104 (s : N.State) (i : N.Inputs) :
  R.v26104 (state s) (inputs i) = Zmod.unsigned (N.v26104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26104 s i)) at 1.
  unfold R.v26104, N.v26104.
  rewrite ?node_26099.
  rewrite ?node_26103.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26105 (s : N.State) (i : N.Inputs) :
  R.v26105 (state s) (inputs i) = Zmod.unsigned (N.v26105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26105 s i)) at 1.
  unfold R.v26105, N.v26105.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26106 (s : N.State) (i : N.Inputs) :
  R.v26106 (state s) (inputs i) = Zmod.unsigned (N.v26106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26106 s i)) at 1.
  unfold R.v26106, N.v26106.
  unfold R.v16463, N.v16463.
  rewrite !state_r1052_nr_5F1052.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1052_nr_5F1052 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26107 (s : N.State) (i : N.Inputs) :
  R.v26107 (state s) (inputs i) = Zmod.unsigned (N.v26107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26107 s i)) at 1.
  unfold R.v26107, N.v26107.
  unfold R.v6, N.v6.
  rewrite !state_r1051_nr_5F1051.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1051_nr_5F1051 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26108 (s : N.State) (i : N.Inputs) :
  R.v26108 (state s) (inputs i) = Zmod.unsigned (N.v26108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26108 s i)) at 1.
  unfold R.v26108, N.v26108.
  unfold R.v6, N.v6.
  rewrite !state_r1050_nr_5F1050.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1050_nr_5F1050 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26109 (s : N.State) (i : N.Inputs) :
  R.v26109 (state s) (inputs i) = Zmod.unsigned (N.v26109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26109 s i)) at 1.
  unfold R.v26109, N.v26109.
  rewrite ?node_26107.
  rewrite ?node_26108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26110 (s : N.State) (i : N.Inputs) :
  R.v26110 (state s) (inputs i) = Zmod.unsigned (N.v26110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26110 s i)) at 1.
  unfold R.v26110, N.v26110.
  unfold R.v16484, N.v16484.
  rewrite ?node_26109.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26111 (s : N.State) (i : N.Inputs) :
  R.v26111 (state s) (inputs i) = Zmod.unsigned (N.v26111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26111 s i)) at 1.
  unfold R.v26111, N.v26111.
  rewrite ?node_26106.
  rewrite ?node_26110.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26112 (s : N.State) (i : N.Inputs) :
  R.v26112 (state s) (inputs i) = Zmod.unsigned (N.v26112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26112 s i)) at 1.
  unfold R.v26112, N.v26112.
  unfold R.v6, N.v6.
  rewrite ?node_26111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26113 (s : N.State) (i : N.Inputs) :
  R.v26113 (state s) (inputs i) = Zmod.unsigned (N.v26113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26113 s i)) at 1.
  unfold R.v26113, N.v26113.
  rewrite ?node_9876.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26114 (s : N.State) (i : N.Inputs) :
  R.v26114 (state s) (inputs i) = Zmod.unsigned (N.v26114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26114 s i)) at 1.
  unfold R.v26114, N.v26114.
  unfold R.v6, N.v6.
  rewrite ?node_10032.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26115 (s : N.State) (i : N.Inputs) :
  R.v26115 (state s) (inputs i) = Zmod.unsigned (N.v26115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26115 s i)) at 1.
  unfold R.v26115, N.v26115.
  rewrite ?node_26113.
  rewrite ?node_26114.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26116 (s : N.State) (i : N.Inputs) :
  R.v26116 (state s) (inputs i) = Zmod.unsigned (N.v26116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26116 s i)) at 1.
  unfold R.v26116, N.v26116.
  rewrite ?node_26112.
  rewrite ?node_26115.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26117 (s : N.State) (i : N.Inputs) :
  R.v26117 (state s) (inputs i) = Zmod.unsigned (N.v26117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26117 s i)) at 1.
  unfold R.v26117, N.v26117.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26118 (s : N.State) (i : N.Inputs) :
  R.v26118 (state s) (inputs i) = Zmod.unsigned (N.v26118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26118 s i)) at 1.
  unfold R.v26118, N.v26118.
  rewrite ?node_9880.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26119 (s : N.State) (i : N.Inputs) :
  R.v26119 (state s) (inputs i) = Zmod.unsigned (N.v26119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26119 s i)) at 1.
  unfold R.v26119, N.v26119.
  unfold R.v6, N.v6.
  rewrite !state_r1053_nr_5F1053.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1053_nr_5F1053 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26120 (s : N.State) (i : N.Inputs) :
  R.v26120 (state s) (inputs i) = Zmod.unsigned (N.v26120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26120 s i)) at 1.
  unfold R.v26120, N.v26120.
  unfold R.v6, N.v6.
  rewrite ?node_9876.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26121 (s : N.State) (i : N.Inputs) :
  R.v26121 (state s) (inputs i) = Zmod.unsigned (N.v26121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26121 s i)) at 1.
  unfold R.v26121, N.v26121.
  rewrite ?node_26119.
  rewrite ?node_26120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26122 (s : N.State) (i : N.Inputs) :
  R.v26122 (state s) (inputs i) = Zmod.unsigned (N.v26122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26122 s i)) at 1.
  unfold R.v26122, N.v26122.
  unfold R.v16484, N.v16484.
  rewrite ?node_26121.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26123 (s : N.State) (i : N.Inputs) :
  R.v26123 (state s) (inputs i) = Zmod.unsigned (N.v26123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26123 s i)) at 1.
  unfold R.v26123, N.v26123.
  rewrite ?node_26118.
  rewrite ?node_26122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26124 (s : N.State) (i : N.Inputs) :
  R.v26124 (state s) (inputs i) = Zmod.unsigned (N.v26124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26124 s i)) at 1.
  unfold R.v26124, N.v26124.
  unfold R.v6, N.v6.
  rewrite ?node_26123.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26125 (s : N.State) (i : N.Inputs) :
  R.v26125 (state s) (inputs i) = Zmod.unsigned (N.v26125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26125 s i)) at 1.
  unfold R.v26125, N.v26125.
  rewrite ?node_9881.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26126 (s : N.State) (i : N.Inputs) :
  R.v26126 (state s) (inputs i) = Zmod.unsigned (N.v26126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26126 s i)) at 1.
  unfold R.v26126, N.v26126.
  unfold R.v6, N.v6.
  rewrite ?node_10083.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26127 (s : N.State) (i : N.Inputs) :
  R.v26127 (state s) (inputs i) = Zmod.unsigned (N.v26127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26127 s i)) at 1.
  unfold R.v26127, N.v26127.
  rewrite ?node_26125.
  rewrite ?node_26126.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26128 (s : N.State) (i : N.Inputs) :
  R.v26128 (state s) (inputs i) = Zmod.unsigned (N.v26128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26128 s i)) at 1.
  unfold R.v26128, N.v26128.
  rewrite ?node_26124.
  rewrite ?node_26127.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26129 (s : N.State) (i : N.Inputs) :
  R.v26129 (state s) (inputs i) = Zmod.unsigned (N.v26129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26129 s i)) at 1.
  unfold R.v26129, N.v26129.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26130 (s : N.State) (i : N.Inputs) :
  R.v26130 (state s) (inputs i) = Zmod.unsigned (N.v26130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26130 s i)) at 1.
  unfold R.v26130, N.v26130.
  rewrite ?node_9974.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26131 (s : N.State) (i : N.Inputs) :
  R.v26131 (state s) (inputs i) = Zmod.unsigned (N.v26131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26131 s i)) at 1.
  unfold R.v26131, N.v26131.
  unfold R.v16463, N.v16463.
  rewrite !state_r1057_nr_5F1057.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1057_nr_5F1057 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26132 (s : N.State) (i : N.Inputs) :
  R.v26132 (state s) (inputs i) = Zmod.unsigned (N.v26132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26132 s i)) at 1.
  unfold R.v26132, N.v26132.
  unfold R.v16463, N.v16463.
  rewrite !state_r1056_nr_5F1056.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1056_nr_5F1056 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26133 (s : N.State) (i : N.Inputs) :
  R.v26133 (state s) (inputs i) = Zmod.unsigned (N.v26133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26133 s i)) at 1.
  unfold R.v26133, N.v26133.
  unfold R.v6, N.v6.
  rewrite !state_r1055_nr_5F1055.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1055_nr_5F1055 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26134 (s : N.State) (i : N.Inputs) :
  R.v26134 (state s) (inputs i) = Zmod.unsigned (N.v26134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26134 s i)) at 1.
  unfold R.v26134, N.v26134.
  unfold R.v6, N.v6.
  rewrite !state_r1054_nr_5F1054.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1054_nr_5F1054 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26135 (s : N.State) (i : N.Inputs) :
  R.v26135 (state s) (inputs i) = Zmod.unsigned (N.v26135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26135 s i)) at 1.
  unfold R.v26135, N.v26135.
  rewrite ?node_26133.
  rewrite ?node_26134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26136 (s : N.State) (i : N.Inputs) :
  R.v26136 (state s) (inputs i) = Zmod.unsigned (N.v26136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26136 s i)) at 1.
  unfold R.v26136, N.v26136.
  unfold R.v16484, N.v16484.
  rewrite ?node_26135.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26137 (s : N.State) (i : N.Inputs) :
  R.v26137 (state s) (inputs i) = Zmod.unsigned (N.v26137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26137 s i)) at 1.
  unfold R.v26137, N.v26137.
  rewrite ?node_26130.
  rewrite ?node_26131.
  rewrite ?node_26132.
  rewrite ?node_26136.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26138 (s : N.State) (i : N.Inputs) :
  R.v26138 (state s) (inputs i) = Zmod.unsigned (N.v26138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26138 s i)) at 1.
  unfold R.v26138, N.v26138.
  unfold R.v6, N.v6.
  rewrite ?node_26137.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26139 (s : N.State) (i : N.Inputs) :
  R.v26139 (state s) (inputs i) = Zmod.unsigned (N.v26139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26139 s i)) at 1.
  unfold R.v26139, N.v26139.
  rewrite ?node_9975.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26140 (s : N.State) (i : N.Inputs) :
  R.v26140 (state s) (inputs i) = Zmod.unsigned (N.v26140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26140 s i)) at 1.
  unfold R.v26140, N.v26140.
  unfold R.v6, N.v6.
  rewrite ?node_10129.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26141 (s : N.State) (i : N.Inputs) :
  R.v26141 (state s) (inputs i) = Zmod.unsigned (N.v26141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26141 s i)) at 1.
  unfold R.v26141, N.v26141.
  unfold R.v6, N.v6.
  rewrite ?node_10197.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26142 (s : N.State) (i : N.Inputs) :
  R.v26142 (state s) (inputs i) = Zmod.unsigned (N.v26142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26142 s i)) at 1.
  unfold R.v26142, N.v26142.
  rewrite ?node_26139.
  rewrite ?node_26140.
  rewrite ?node_26141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26143 (s : N.State) (i : N.Inputs) :
  R.v26143 (state s) (inputs i) = Zmod.unsigned (N.v26143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26143 s i)) at 1.
  unfold R.v26143, N.v26143.
  rewrite ?node_26138.
  rewrite ?node_26142.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26144 (s : N.State) (i : N.Inputs) :
  R.v26144 (state s) (inputs i) = Zmod.unsigned (N.v26144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26144 s i)) at 1.
  unfold R.v26144, N.v26144.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26145 (s : N.State) (i : N.Inputs) :
  R.v26145 (state s) (inputs i) = Zmod.unsigned (N.v26145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26145 s i)) at 1.
  unfold R.v26145, N.v26145.
  unfold R.v16463, N.v16463.
  rewrite !state_r1056_nr_5F1056.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1056_nr_5F1056 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26146 (s : N.State) (i : N.Inputs) :
  R.v26146 (state s) (inputs i) = Zmod.unsigned (N.v26146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26146 s i)) at 1.
  unfold R.v26146, N.v26146.
  unfold R.v6, N.v6.
  rewrite !state_r1055_nr_5F1055.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1055_nr_5F1055 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26147 (s : N.State) (i : N.Inputs) :
  R.v26147 (state s) (inputs i) = Zmod.unsigned (N.v26147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26147 s i)) at 1.
  unfold R.v26147, N.v26147.
  unfold R.v6, N.v6.
  rewrite !state_r1054_nr_5F1054.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1054_nr_5F1054 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26148 (s : N.State) (i : N.Inputs) :
  R.v26148 (state s) (inputs i) = Zmod.unsigned (N.v26148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26148 s i)) at 1.
  unfold R.v26148, N.v26148.
  rewrite ?node_26146.
  rewrite ?node_26147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26149 (s : N.State) (i : N.Inputs) :
  R.v26149 (state s) (inputs i) = Zmod.unsigned (N.v26149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26149 s i)) at 1.
  unfold R.v26149, N.v26149.
  unfold R.v16484, N.v16484.
  rewrite ?node_26148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26150 (s : N.State) (i : N.Inputs) :
  R.v26150 (state s) (inputs i) = Zmod.unsigned (N.v26150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26150 s i)) at 1.
  unfold R.v26150, N.v26150.
  rewrite ?node_26145.
  rewrite ?node_26149.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26151 (s : N.State) (i : N.Inputs) :
  R.v26151 (state s) (inputs i) = Zmod.unsigned (N.v26151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26151 s i)) at 1.
  unfold R.v26151, N.v26151.
  unfold R.v6, N.v6.
  rewrite ?node_26150.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26152 (s : N.State) (i : N.Inputs) :
  R.v26152 (state s) (inputs i) = Zmod.unsigned (N.v26152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26152 s i)) at 1.
  unfold R.v26152, N.v26152.
  rewrite ?node_9970.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26153 (s : N.State) (i : N.Inputs) :
  R.v26153 (state s) (inputs i) = Zmod.unsigned (N.v26153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26153 s i)) at 1.
  unfold R.v26153, N.v26153.
  unfold R.v6, N.v6.
  rewrite ?node_10129.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26154 (s : N.State) (i : N.Inputs) :
  R.v26154 (state s) (inputs i) = Zmod.unsigned (N.v26154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26154 s i)) at 1.
  unfold R.v26154, N.v26154.
  rewrite ?node_26152.
  rewrite ?node_26153.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26155 (s : N.State) (i : N.Inputs) :
  R.v26155 (state s) (inputs i) = Zmod.unsigned (N.v26155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26155 s i)) at 1.
  unfold R.v26155, N.v26155.
  rewrite ?node_26151.
  rewrite ?node_26154.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26156 (s : N.State) (i : N.Inputs) :
  R.v26156 (state s) (inputs i) = Zmod.unsigned (N.v26156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26156 s i)) at 1.
  unfold R.v26156, N.v26156.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26157 (s : N.State) (i : N.Inputs) :
  R.v26157 (state s) (inputs i) = Zmod.unsigned (N.v26157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26157 s i)) at 1.
  unfold R.v26157, N.v26157.
  rewrite ?node_9974.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26158 (s : N.State) (i : N.Inputs) :
  R.v26158 (state s) (inputs i) = Zmod.unsigned (N.v26158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26158 s i)) at 1.
  unfold R.v26158, N.v26158.
  unfold R.v6, N.v6.
  rewrite !state_r1057_nr_5F1057.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1057_nr_5F1057 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26159 (s : N.State) (i : N.Inputs) :
  R.v26159 (state s) (inputs i) = Zmod.unsigned (N.v26159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26159 s i)) at 1.
  unfold R.v26159, N.v26159.
  unfold R.v6, N.v6.
  rewrite ?node_9970.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26160 (s : N.State) (i : N.Inputs) :
  R.v26160 (state s) (inputs i) = Zmod.unsigned (N.v26160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26160 s i)) at 1.
  unfold R.v26160, N.v26160.
  rewrite ?node_26158.
  rewrite ?node_26159.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26161 (s : N.State) (i : N.Inputs) :
  R.v26161 (state s) (inputs i) = Zmod.unsigned (N.v26161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26161 s i)) at 1.
  unfold R.v26161, N.v26161.
  unfold R.v16484, N.v16484.
  rewrite ?node_26160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26162 (s : N.State) (i : N.Inputs) :
  R.v26162 (state s) (inputs i) = Zmod.unsigned (N.v26162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26162 s i)) at 1.
  unfold R.v26162, N.v26162.
  rewrite ?node_26157.
  rewrite ?node_26161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26163 (s : N.State) (i : N.Inputs) :
  R.v26163 (state s) (inputs i) = Zmod.unsigned (N.v26163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26163 s i)) at 1.
  unfold R.v26163, N.v26163.
  unfold R.v6, N.v6.
  rewrite ?node_26162.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26164 (s : N.State) (i : N.Inputs) :
  R.v26164 (state s) (inputs i) = Zmod.unsigned (N.v26164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26164 s i)) at 1.
  unfold R.v26164, N.v26164.
  rewrite ?node_9975.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26165 (s : N.State) (i : N.Inputs) :
  R.v26165 (state s) (inputs i) = Zmod.unsigned (N.v26165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26165 s i)) at 1.
  unfold R.v26165, N.v26165.
  unfold R.v6, N.v6.
  rewrite ?node_10197.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26166 (s : N.State) (i : N.Inputs) :
  R.v26166 (state s) (inputs i) = Zmod.unsigned (N.v26166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26166 s i)) at 1.
  unfold R.v26166, N.v26166.
  rewrite ?node_26164.
  rewrite ?node_26165.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26167 (s : N.State) (i : N.Inputs) :
  R.v26167 (state s) (inputs i) = Zmod.unsigned (N.v26167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26167 s i)) at 1.
  unfold R.v26167, N.v26167.
  rewrite ?node_26163.
  rewrite ?node_26166.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26168 (s : N.State) (i : N.Inputs) :
  R.v26168 (state s) (inputs i) = Zmod.unsigned (N.v26168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26168 s i)) at 1.
  unfold R.v26168, N.v26168.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26169 (s : N.State) (i : N.Inputs) :
  R.v26169 (state s) (inputs i) = Zmod.unsigned (N.v26169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26169 s i)) at 1.
  unfold R.v26169, N.v26169.
  rewrite ?node_9981.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26170 (s : N.State) (i : N.Inputs) :
  R.v26170 (state s) (inputs i) = Zmod.unsigned (N.v26170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26170 s i)) at 1.
  unfold R.v26170, N.v26170.
  unfold R.v16463, N.v16463.
  rewrite !state_r1061_nr_5F1061.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1061_nr_5F1061 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26171 (s : N.State) (i : N.Inputs) :
  R.v26171 (state s) (inputs i) = Zmod.unsigned (N.v26171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26171 s i)) at 1.
  unfold R.v26171, N.v26171.
  unfold R.v16463, N.v16463.
  rewrite !state_r1060_nr_5F1060.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1060_nr_5F1060 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26172 (s : N.State) (i : N.Inputs) :
  R.v26172 (state s) (inputs i) = Zmod.unsigned (N.v26172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26172 s i)) at 1.
  unfold R.v26172, N.v26172.
  unfold R.v6, N.v6.
  rewrite !state_r1059_nr_5F1059.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1059_nr_5F1059 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26173 (s : N.State) (i : N.Inputs) :
  R.v26173 (state s) (inputs i) = Zmod.unsigned (N.v26173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26173 s i)) at 1.
  unfold R.v26173, N.v26173.
  unfold R.v6, N.v6.
  rewrite !state_r1058_nr_5F1058.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1058_nr_5F1058 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26174 (s : N.State) (i : N.Inputs) :
  R.v26174 (state s) (inputs i) = Zmod.unsigned (N.v26174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26174 s i)) at 1.
  unfold R.v26174, N.v26174.
  rewrite ?node_26172.
  rewrite ?node_26173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26175 (s : N.State) (i : N.Inputs) :
  R.v26175 (state s) (inputs i) = Zmod.unsigned (N.v26175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26175 s i)) at 1.
  unfold R.v26175, N.v26175.
  unfold R.v16484, N.v16484.
  rewrite ?node_26174.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26176 (s : N.State) (i : N.Inputs) :
  R.v26176 (state s) (inputs i) = Zmod.unsigned (N.v26176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26176 s i)) at 1.
  unfold R.v26176, N.v26176.
  rewrite ?node_26169.
  rewrite ?node_26170.
  rewrite ?node_26171.
  rewrite ?node_26175.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26177 (s : N.State) (i : N.Inputs) :
  R.v26177 (state s) (inputs i) = Zmod.unsigned (N.v26177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26177 s i)) at 1.
  unfold R.v26177, N.v26177.
  unfold R.v6, N.v6.
  rewrite ?node_26176.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26178 (s : N.State) (i : N.Inputs) :
  R.v26178 (state s) (inputs i) = Zmod.unsigned (N.v26178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26178 s i)) at 1.
  unfold R.v26178, N.v26178.
  rewrite ?node_9982.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26179 (s : N.State) (i : N.Inputs) :
  R.v26179 (state s) (inputs i) = Zmod.unsigned (N.v26179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26179 s i)) at 1.
  unfold R.v26179, N.v26179.
  unfold R.v6, N.v6.
  rewrite ?node_10136.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26180 (s : N.State) (i : N.Inputs) :
  R.v26180 (state s) (inputs i) = Zmod.unsigned (N.v26180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26180 s i)) at 1.
  unfold R.v26180, N.v26180.
  unfold R.v6, N.v6.
  rewrite ?node_10201.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26181 (s : N.State) (i : N.Inputs) :
  R.v26181 (state s) (inputs i) = Zmod.unsigned (N.v26181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26181 s i)) at 1.
  unfold R.v26181, N.v26181.
  rewrite ?node_26178.
  rewrite ?node_26179.
  rewrite ?node_26180.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26182 (s : N.State) (i : N.Inputs) :
  R.v26182 (state s) (inputs i) = Zmod.unsigned (N.v26182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26182 s i)) at 1.
  unfold R.v26182, N.v26182.
  rewrite ?node_26177.
  rewrite ?node_26181.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26183 (s : N.State) (i : N.Inputs) :
  R.v26183 (state s) (inputs i) = Zmod.unsigned (N.v26183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26183 s i)) at 1.
  unfold R.v26183, N.v26183.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26184 (s : N.State) (i : N.Inputs) :
  R.v26184 (state s) (inputs i) = Zmod.unsigned (N.v26184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26184 s i)) at 1.
  unfold R.v26184, N.v26184.
  unfold R.v16463, N.v16463.
  rewrite !state_r1060_nr_5F1060.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1060_nr_5F1060 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26185 (s : N.State) (i : N.Inputs) :
  R.v26185 (state s) (inputs i) = Zmod.unsigned (N.v26185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26185 s i)) at 1.
  unfold R.v26185, N.v26185.
  unfold R.v6, N.v6.
  rewrite !state_r1059_nr_5F1059.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1059_nr_5F1059 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26186 (s : N.State) (i : N.Inputs) :
  R.v26186 (state s) (inputs i) = Zmod.unsigned (N.v26186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26186 s i)) at 1.
  unfold R.v26186, N.v26186.
  unfold R.v6, N.v6.
  rewrite !state_r1058_nr_5F1058.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1058_nr_5F1058 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26187 (s : N.State) (i : N.Inputs) :
  R.v26187 (state s) (inputs i) = Zmod.unsigned (N.v26187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26187 s i)) at 1.
  unfold R.v26187, N.v26187.
  rewrite ?node_26185.
  rewrite ?node_26186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26188 (s : N.State) (i : N.Inputs) :
  R.v26188 (state s) (inputs i) = Zmod.unsigned (N.v26188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26188 s i)) at 1.
  unfold R.v26188, N.v26188.
  unfold R.v16484, N.v16484.
  rewrite ?node_26187.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26189 (s : N.State) (i : N.Inputs) :
  R.v26189 (state s) (inputs i) = Zmod.unsigned (N.v26189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26189 s i)) at 1.
  unfold R.v26189, N.v26189.
  rewrite ?node_26184.
  rewrite ?node_26188.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26190 (s : N.State) (i : N.Inputs) :
  R.v26190 (state s) (inputs i) = Zmod.unsigned (N.v26190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26190 s i)) at 1.
  unfold R.v26190, N.v26190.
  unfold R.v6, N.v6.
  rewrite ?node_26189.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26191 (s : N.State) (i : N.Inputs) :
  R.v26191 (state s) (inputs i) = Zmod.unsigned (N.v26191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26191 s i)) at 1.
  unfold R.v26191, N.v26191.
  rewrite ?node_9977.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26192 (s : N.State) (i : N.Inputs) :
  R.v26192 (state s) (inputs i) = Zmod.unsigned (N.v26192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26192 s i)) at 1.
  unfold R.v26192, N.v26192.
  unfold R.v6, N.v6.
  rewrite ?node_10136.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26193 (s : N.State) (i : N.Inputs) :
  R.v26193 (state s) (inputs i) = Zmod.unsigned (N.v26193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26193 s i)) at 1.
  unfold R.v26193, N.v26193.
  rewrite ?node_26191.
  rewrite ?node_26192.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26194 (s : N.State) (i : N.Inputs) :
  R.v26194 (state s) (inputs i) = Zmod.unsigned (N.v26194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26194 s i)) at 1.
  unfold R.v26194, N.v26194.
  rewrite ?node_26190.
  rewrite ?node_26193.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26195 (s : N.State) (i : N.Inputs) :
  R.v26195 (state s) (inputs i) = Zmod.unsigned (N.v26195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26195 s i)) at 1.
  unfold R.v26195, N.v26195.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26196 (s : N.State) (i : N.Inputs) :
  R.v26196 (state s) (inputs i) = Zmod.unsigned (N.v26196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26196 s i)) at 1.
  unfold R.v26196, N.v26196.
  rewrite ?node_9981.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26197 (s : N.State) (i : N.Inputs) :
  R.v26197 (state s) (inputs i) = Zmod.unsigned (N.v26197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26197 s i)) at 1.
  unfold R.v26197, N.v26197.
  unfold R.v6, N.v6.
  rewrite !state_r1061_nr_5F1061.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1061_nr_5F1061 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26198 (s : N.State) (i : N.Inputs) :
  R.v26198 (state s) (inputs i) = Zmod.unsigned (N.v26198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26198 s i)) at 1.
  unfold R.v26198, N.v26198.
  unfold R.v6, N.v6.
  rewrite ?node_9977.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26199 (s : N.State) (i : N.Inputs) :
  R.v26199 (state s) (inputs i) = Zmod.unsigned (N.v26199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26199 s i)) at 1.
  unfold R.v26199, N.v26199.
  rewrite ?node_26197.
  rewrite ?node_26198.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26200 (s : N.State) (i : N.Inputs) :
  R.v26200 (state s) (inputs i) = Zmod.unsigned (N.v26200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26200 s i)) at 1.
  unfold R.v26200, N.v26200.
  unfold R.v16484, N.v16484.
  rewrite ?node_26199.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26201 (s : N.State) (i : N.Inputs) :
  R.v26201 (state s) (inputs i) = Zmod.unsigned (N.v26201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26201 s i)) at 1.
  unfold R.v26201, N.v26201.
  rewrite ?node_26196.
  rewrite ?node_26200.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26202 (s : N.State) (i : N.Inputs) :
  R.v26202 (state s) (inputs i) = Zmod.unsigned (N.v26202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26202 s i)) at 1.
  unfold R.v26202, N.v26202.
  unfold R.v6, N.v6.
  rewrite ?node_26201.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26203 (s : N.State) (i : N.Inputs) :
  R.v26203 (state s) (inputs i) = Zmod.unsigned (N.v26203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26203 s i)) at 1.
  unfold R.v26203, N.v26203.
  rewrite ?node_9982.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26204 (s : N.State) (i : N.Inputs) :
  R.v26204 (state s) (inputs i) = Zmod.unsigned (N.v26204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26204 s i)) at 1.
  unfold R.v26204, N.v26204.
  unfold R.v6, N.v6.
  rewrite ?node_10201.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26205 (s : N.State) (i : N.Inputs) :
  R.v26205 (state s) (inputs i) = Zmod.unsigned (N.v26205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26205 s i)) at 1.
  unfold R.v26205, N.v26205.
  rewrite ?node_26203.
  rewrite ?node_26204.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26206 (s : N.State) (i : N.Inputs) :
  R.v26206 (state s) (inputs i) = Zmod.unsigned (N.v26206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26206 s i)) at 1.
  unfold R.v26206, N.v26206.
  rewrite ?node_26202.
  rewrite ?node_26205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26207 (s : N.State) (i : N.Inputs) :
  R.v26207 (state s) (inputs i) = Zmod.unsigned (N.v26207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26207 s i)) at 1.
  unfold R.v26207, N.v26207.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26208 (s : N.State) (i : N.Inputs) :
  R.v26208 (state s) (inputs i) = Zmod.unsigned (N.v26208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26208 s i)) at 1.
  unfold R.v26208, N.v26208.
  rewrite ?node_9989.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26209 (s : N.State) (i : N.Inputs) :
  R.v26209 (state s) (inputs i) = Zmod.unsigned (N.v26209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26209 s i)) at 1.
  unfold R.v26209, N.v26209.
  unfold R.v16463, N.v16463.
  rewrite !state_r1065_nr_5F1065.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1065_nr_5F1065 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26210 (s : N.State) (i : N.Inputs) :
  R.v26210 (state s) (inputs i) = Zmod.unsigned (N.v26210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26210 s i)) at 1.
  unfold R.v26210, N.v26210.
  unfold R.v16463, N.v16463.
  rewrite !state_r1064_nr_5F1064.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1064_nr_5F1064 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26211 (s : N.State) (i : N.Inputs) :
  R.v26211 (state s) (inputs i) = Zmod.unsigned (N.v26211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26211 s i)) at 1.
  unfold R.v26211, N.v26211.
  unfold R.v6, N.v6.
  rewrite !state_r1063_nr_5F1063.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1063_nr_5F1063 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26212 (s : N.State) (i : N.Inputs) :
  R.v26212 (state s) (inputs i) = Zmod.unsigned (N.v26212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26212 s i)) at 1.
  unfold R.v26212, N.v26212.
  unfold R.v6, N.v6.
  rewrite !state_r1062_nr_5F1062.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1062_nr_5F1062 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26213 (s : N.State) (i : N.Inputs) :
  R.v26213 (state s) (inputs i) = Zmod.unsigned (N.v26213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26213 s i)) at 1.
  unfold R.v26213, N.v26213.
  rewrite ?node_26211.
  rewrite ?node_26212.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26214 (s : N.State) (i : N.Inputs) :
  R.v26214 (state s) (inputs i) = Zmod.unsigned (N.v26214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26214 s i)) at 1.
  unfold R.v26214, N.v26214.
  unfold R.v16484, N.v16484.
  rewrite ?node_26213.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26215 (s : N.State) (i : N.Inputs) :
  R.v26215 (state s) (inputs i) = Zmod.unsigned (N.v26215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26215 s i)) at 1.
  unfold R.v26215, N.v26215.
  rewrite ?node_26208.
  rewrite ?node_26209.
  rewrite ?node_26210.
  rewrite ?node_26214.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26216 (s : N.State) (i : N.Inputs) :
  R.v26216 (state s) (inputs i) = Zmod.unsigned (N.v26216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26216 s i)) at 1.
  unfold R.v26216, N.v26216.
  unfold R.v6, N.v6.
  rewrite ?node_26215.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26217 (s : N.State) (i : N.Inputs) :
  R.v26217 (state s) (inputs i) = Zmod.unsigned (N.v26217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26217 s i)) at 1.
  unfold R.v26217, N.v26217.
  rewrite ?node_9990.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26218 (s : N.State) (i : N.Inputs) :
  R.v26218 (state s) (inputs i) = Zmod.unsigned (N.v26218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26218 s i)) at 1.
  unfold R.v26218, N.v26218.
  unfold R.v6, N.v6.
  rewrite ?node_10144.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26219 (s : N.State) (i : N.Inputs) :
  R.v26219 (state s) (inputs i) = Zmod.unsigned (N.v26219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26219 s i)) at 1.
  unfold R.v26219, N.v26219.
  unfold R.v6, N.v6.
  rewrite ?node_10205.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26220 (s : N.State) (i : N.Inputs) :
  R.v26220 (state s) (inputs i) = Zmod.unsigned (N.v26220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26220 s i)) at 1.
  unfold R.v26220, N.v26220.
  rewrite ?node_26217.
  rewrite ?node_26218.
  rewrite ?node_26219.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26221 (s : N.State) (i : N.Inputs) :
  R.v26221 (state s) (inputs i) = Zmod.unsigned (N.v26221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26221 s i)) at 1.
  unfold R.v26221, N.v26221.
  rewrite ?node_26216.
  rewrite ?node_26220.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26222 (s : N.State) (i : N.Inputs) :
  R.v26222 (state s) (inputs i) = Zmod.unsigned (N.v26222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26222 s i)) at 1.
  unfold R.v26222, N.v26222.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26223 (s : N.State) (i : N.Inputs) :
  R.v26223 (state s) (inputs i) = Zmod.unsigned (N.v26223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26223 s i)) at 1.
  unfold R.v26223, N.v26223.
  unfold R.v16463, N.v16463.
  rewrite !state_r1064_nr_5F1064.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1064_nr_5F1064 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26224 (s : N.State) (i : N.Inputs) :
  R.v26224 (state s) (inputs i) = Zmod.unsigned (N.v26224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26224 s i)) at 1.
  unfold R.v26224, N.v26224.
  unfold R.v6, N.v6.
  rewrite !state_r1063_nr_5F1063.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1063_nr_5F1063 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26225 (s : N.State) (i : N.Inputs) :
  R.v26225 (state s) (inputs i) = Zmod.unsigned (N.v26225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26225 s i)) at 1.
  unfold R.v26225, N.v26225.
  unfold R.v6, N.v6.
  rewrite !state_r1062_nr_5F1062.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1062_nr_5F1062 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26226 (s : N.State) (i : N.Inputs) :
  R.v26226 (state s) (inputs i) = Zmod.unsigned (N.v26226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26226 s i)) at 1.
  unfold R.v26226, N.v26226.
  rewrite ?node_26224.
  rewrite ?node_26225.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26227 (s : N.State) (i : N.Inputs) :
  R.v26227 (state s) (inputs i) = Zmod.unsigned (N.v26227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26227 s i)) at 1.
  unfold R.v26227, N.v26227.
  unfold R.v16484, N.v16484.
  rewrite ?node_26226.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26228 (s : N.State) (i : N.Inputs) :
  R.v26228 (state s) (inputs i) = Zmod.unsigned (N.v26228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26228 s i)) at 1.
  unfold R.v26228, N.v26228.
  rewrite ?node_26223.
  rewrite ?node_26227.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26229 (s : N.State) (i : N.Inputs) :
  R.v26229 (state s) (inputs i) = Zmod.unsigned (N.v26229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26229 s i)) at 1.
  unfold R.v26229, N.v26229.
  unfold R.v6, N.v6.
  rewrite ?node_26228.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26230 (s : N.State) (i : N.Inputs) :
  R.v26230 (state s) (inputs i) = Zmod.unsigned (N.v26230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26230 s i)) at 1.
  unfold R.v26230, N.v26230.
  rewrite ?node_9985.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26231 (s : N.State) (i : N.Inputs) :
  R.v26231 (state s) (inputs i) = Zmod.unsigned (N.v26231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26231 s i)) at 1.
  unfold R.v26231, N.v26231.
  unfold R.v6, N.v6.
  rewrite ?node_10144.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26232 (s : N.State) (i : N.Inputs) :
  R.v26232 (state s) (inputs i) = Zmod.unsigned (N.v26232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26232 s i)) at 1.
  unfold R.v26232, N.v26232.
  rewrite ?node_26230.
  rewrite ?node_26231.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26233 (s : N.State) (i : N.Inputs) :
  R.v26233 (state s) (inputs i) = Zmod.unsigned (N.v26233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26233 s i)) at 1.
  unfold R.v26233, N.v26233.
  rewrite ?node_26229.
  rewrite ?node_26232.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26234 (s : N.State) (i : N.Inputs) :
  R.v26234 (state s) (inputs i) = Zmod.unsigned (N.v26234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26234 s i)) at 1.
  unfold R.v26234, N.v26234.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26235 (s : N.State) (i : N.Inputs) :
  R.v26235 (state s) (inputs i) = Zmod.unsigned (N.v26235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26235 s i)) at 1.
  unfold R.v26235, N.v26235.
  rewrite ?node_9989.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26236 (s : N.State) (i : N.Inputs) :
  R.v26236 (state s) (inputs i) = Zmod.unsigned (N.v26236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26236 s i)) at 1.
  unfold R.v26236, N.v26236.
  unfold R.v6, N.v6.
  rewrite !state_r1065_nr_5F1065.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1065_nr_5F1065 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26237 (s : N.State) (i : N.Inputs) :
  R.v26237 (state s) (inputs i) = Zmod.unsigned (N.v26237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26237 s i)) at 1.
  unfold R.v26237, N.v26237.
  unfold R.v6, N.v6.
  rewrite ?node_9985.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26238 (s : N.State) (i : N.Inputs) :
  R.v26238 (state s) (inputs i) = Zmod.unsigned (N.v26238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26238 s i)) at 1.
  unfold R.v26238, N.v26238.
  rewrite ?node_26236.
  rewrite ?node_26237.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26239 (s : N.State) (i : N.Inputs) :
  R.v26239 (state s) (inputs i) = Zmod.unsigned (N.v26239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26239 s i)) at 1.
  unfold R.v26239, N.v26239.
  unfold R.v16484, N.v16484.
  rewrite ?node_26238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26240 (s : N.State) (i : N.Inputs) :
  R.v26240 (state s) (inputs i) = Zmod.unsigned (N.v26240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26240 s i)) at 1.
  unfold R.v26240, N.v26240.
  rewrite ?node_26235.
  rewrite ?node_26239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26241 (s : N.State) (i : N.Inputs) :
  R.v26241 (state s) (inputs i) = Zmod.unsigned (N.v26241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26241 s i)) at 1.
  unfold R.v26241, N.v26241.
  unfold R.v6, N.v6.
  rewrite ?node_26240.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26242 (s : N.State) (i : N.Inputs) :
  R.v26242 (state s) (inputs i) = Zmod.unsigned (N.v26242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26242 s i)) at 1.
  unfold R.v26242, N.v26242.
  rewrite ?node_9990.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26243 (s : N.State) (i : N.Inputs) :
  R.v26243 (state s) (inputs i) = Zmod.unsigned (N.v26243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26243 s i)) at 1.
  unfold R.v26243, N.v26243.
  unfold R.v6, N.v6.
  rewrite ?node_10205.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26244 (s : N.State) (i : N.Inputs) :
  R.v26244 (state s) (inputs i) = Zmod.unsigned (N.v26244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26244 s i)) at 1.
  unfold R.v26244, N.v26244.
  rewrite ?node_26242.
  rewrite ?node_26243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26245 (s : N.State) (i : N.Inputs) :
  R.v26245 (state s) (inputs i) = Zmod.unsigned (N.v26245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26245 s i)) at 1.
  unfold R.v26245, N.v26245.
  rewrite ?node_26241.
  rewrite ?node_26244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26246 (s : N.State) (i : N.Inputs) :
  R.v26246 (state s) (inputs i) = Zmod.unsigned (N.v26246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26246 s i)) at 1.
  unfold R.v26246, N.v26246.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26247 (s : N.State) (i : N.Inputs) :
  R.v26247 (state s) (inputs i) = Zmod.unsigned (N.v26247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26247 s i)) at 1.
  unfold R.v26247, N.v26247.
  rewrite ?node_9997.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26248 (s : N.State) (i : N.Inputs) :
  R.v26248 (state s) (inputs i) = Zmod.unsigned (N.v26248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26248 s i)) at 1.
  unfold R.v26248, N.v26248.
  unfold R.v16463, N.v16463.
  rewrite !state_r1069_nr_5F1069.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1069_nr_5F1069 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26249 (s : N.State) (i : N.Inputs) :
  R.v26249 (state s) (inputs i) = Zmod.unsigned (N.v26249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26249 s i)) at 1.
  unfold R.v26249, N.v26249.
  unfold R.v16463, N.v16463.
  rewrite !state_r1068_nr_5F1068.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1068_nr_5F1068 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26250 (s : N.State) (i : N.Inputs) :
  R.v26250 (state s) (inputs i) = Zmod.unsigned (N.v26250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26250 s i)) at 1.
  unfold R.v26250, N.v26250.
  unfold R.v6, N.v6.
  rewrite !state_r1067_nr_5F1067.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1067_nr_5F1067 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26251 (s : N.State) (i : N.Inputs) :
  R.v26251 (state s) (inputs i) = Zmod.unsigned (N.v26251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26251 s i)) at 1.
  unfold R.v26251, N.v26251.
  unfold R.v6, N.v6.
  rewrite !state_r1066_nr_5F1066.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1066_nr_5F1066 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26252 (s : N.State) (i : N.Inputs) :
  R.v26252 (state s) (inputs i) = Zmod.unsigned (N.v26252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26252 s i)) at 1.
  unfold R.v26252, N.v26252.
  rewrite ?node_26250.
  rewrite ?node_26251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26253 (s : N.State) (i : N.Inputs) :
  R.v26253 (state s) (inputs i) = Zmod.unsigned (N.v26253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26253 s i)) at 1.
  unfold R.v26253, N.v26253.
  unfold R.v16484, N.v16484.
  rewrite ?node_26252.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26254 (s : N.State) (i : N.Inputs) :
  R.v26254 (state s) (inputs i) = Zmod.unsigned (N.v26254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26254 s i)) at 1.
  unfold R.v26254, N.v26254.
  rewrite ?node_26247.
  rewrite ?node_26248.
  rewrite ?node_26249.
  rewrite ?node_26253.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26255 (s : N.State) (i : N.Inputs) :
  R.v26255 (state s) (inputs i) = Zmod.unsigned (N.v26255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26255 s i)) at 1.
  unfold R.v26255, N.v26255.
  unfold R.v6, N.v6.
  rewrite ?node_26254.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26256 (s : N.State) (i : N.Inputs) :
  R.v26256 (state s) (inputs i) = Zmod.unsigned (N.v26256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26256 s i)) at 1.
  unfold R.v26256, N.v26256.
  rewrite ?node_9998.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26257 (s : N.State) (i : N.Inputs) :
  R.v26257 (state s) (inputs i) = Zmod.unsigned (N.v26257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26257 s i)) at 1.
  unfold R.v26257, N.v26257.
  unfold R.v6, N.v6.
  rewrite ?node_10152.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26258 (s : N.State) (i : N.Inputs) :
  R.v26258 (state s) (inputs i) = Zmod.unsigned (N.v26258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26258 s i)) at 1.
  unfold R.v26258, N.v26258.
  unfold R.v6, N.v6.
  rewrite ?node_10214.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26259 (s : N.State) (i : N.Inputs) :
  R.v26259 (state s) (inputs i) = Zmod.unsigned (N.v26259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26259 s i)) at 1.
  unfold R.v26259, N.v26259.
  rewrite ?node_26256.
  rewrite ?node_26257.
  rewrite ?node_26258.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26260 (s : N.State) (i : N.Inputs) :
  R.v26260 (state s) (inputs i) = Zmod.unsigned (N.v26260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26260 s i)) at 1.
  unfold R.v26260, N.v26260.
  rewrite ?node_26255.
  rewrite ?node_26259.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26261 (s : N.State) (i : N.Inputs) :
  R.v26261 (state s) (inputs i) = Zmod.unsigned (N.v26261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26261 s i)) at 1.
  unfold R.v26261, N.v26261.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26262 (s : N.State) (i : N.Inputs) :
  R.v26262 (state s) (inputs i) = Zmod.unsigned (N.v26262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26262 s i)) at 1.
  unfold R.v26262, N.v26262.
  unfold R.v16463, N.v16463.
  rewrite !state_r1068_nr_5F1068.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1068_nr_5F1068 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26263 (s : N.State) (i : N.Inputs) :
  R.v26263 (state s) (inputs i) = Zmod.unsigned (N.v26263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26263 s i)) at 1.
  unfold R.v26263, N.v26263.
  unfold R.v6, N.v6.
  rewrite !state_r1067_nr_5F1067.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1067_nr_5F1067 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26264 (s : N.State) (i : N.Inputs) :
  R.v26264 (state s) (inputs i) = Zmod.unsigned (N.v26264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26264 s i)) at 1.
  unfold R.v26264, N.v26264.
  unfold R.v6, N.v6.
  rewrite !state_r1066_nr_5F1066.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1066_nr_5F1066 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26265 (s : N.State) (i : N.Inputs) :
  R.v26265 (state s) (inputs i) = Zmod.unsigned (N.v26265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26265 s i)) at 1.
  unfold R.v26265, N.v26265.
  rewrite ?node_26263.
  rewrite ?node_26264.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26266 (s : N.State) (i : N.Inputs) :
  R.v26266 (state s) (inputs i) = Zmod.unsigned (N.v26266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26266 s i)) at 1.
  unfold R.v26266, N.v26266.
  unfold R.v16484, N.v16484.
  rewrite ?node_26265.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26267 (s : N.State) (i : N.Inputs) :
  R.v26267 (state s) (inputs i) = Zmod.unsigned (N.v26267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26267 s i)) at 1.
  unfold R.v26267, N.v26267.
  rewrite ?node_26262.
  rewrite ?node_26266.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26268 (s : N.State) (i : N.Inputs) :
  R.v26268 (state s) (inputs i) = Zmod.unsigned (N.v26268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26268 s i)) at 1.
  unfold R.v26268, N.v26268.
  unfold R.v6, N.v6.
  rewrite ?node_26267.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26269 (s : N.State) (i : N.Inputs) :
  R.v26269 (state s) (inputs i) = Zmod.unsigned (N.v26269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26269 s i)) at 1.
  unfold R.v26269, N.v26269.
  rewrite ?node_9993.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26270 (s : N.State) (i : N.Inputs) :
  R.v26270 (state s) (inputs i) = Zmod.unsigned (N.v26270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26270 s i)) at 1.
  unfold R.v26270, N.v26270.
  unfold R.v6, N.v6.
  rewrite ?node_10152.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26271 (s : N.State) (i : N.Inputs) :
  R.v26271 (state s) (inputs i) = Zmod.unsigned (N.v26271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26271 s i)) at 1.
  unfold R.v26271, N.v26271.
  rewrite ?node_26269.
  rewrite ?node_26270.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26272 (s : N.State) (i : N.Inputs) :
  R.v26272 (state s) (inputs i) = Zmod.unsigned (N.v26272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26272 s i)) at 1.
  unfold R.v26272, N.v26272.
  rewrite ?node_26268.
  rewrite ?node_26271.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26273 (s : N.State) (i : N.Inputs) :
  R.v26273 (state s) (inputs i) = Zmod.unsigned (N.v26273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26273 s i)) at 1.
  unfold R.v26273, N.v26273.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26274 (s : N.State) (i : N.Inputs) :
  R.v26274 (state s) (inputs i) = Zmod.unsigned (N.v26274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26274 s i)) at 1.
  unfold R.v26274, N.v26274.
  rewrite ?node_9997.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26275 (s : N.State) (i : N.Inputs) :
  R.v26275 (state s) (inputs i) = Zmod.unsigned (N.v26275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26275 s i)) at 1.
  unfold R.v26275, N.v26275.
  unfold R.v6, N.v6.
  rewrite !state_r1069_nr_5F1069.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1069_nr_5F1069 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26276 (s : N.State) (i : N.Inputs) :
  R.v26276 (state s) (inputs i) = Zmod.unsigned (N.v26276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26276 s i)) at 1.
  unfold R.v26276, N.v26276.
  unfold R.v6, N.v6.
  rewrite ?node_9993.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26277 (s : N.State) (i : N.Inputs) :
  R.v26277 (state s) (inputs i) = Zmod.unsigned (N.v26277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26277 s i)) at 1.
  unfold R.v26277, N.v26277.
  rewrite ?node_26275.
  rewrite ?node_26276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26278 (s : N.State) (i : N.Inputs) :
  R.v26278 (state s) (inputs i) = Zmod.unsigned (N.v26278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26278 s i)) at 1.
  unfold R.v26278, N.v26278.
  unfold R.v16484, N.v16484.
  rewrite ?node_26277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26279 (s : N.State) (i : N.Inputs) :
  R.v26279 (state s) (inputs i) = Zmod.unsigned (N.v26279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26279 s i)) at 1.
  unfold R.v26279, N.v26279.
  rewrite ?node_26274.
  rewrite ?node_26278.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26280 (s : N.State) (i : N.Inputs) :
  R.v26280 (state s) (inputs i) = Zmod.unsigned (N.v26280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26280 s i)) at 1.
  unfold R.v26280, N.v26280.
  unfold R.v6, N.v6.
  rewrite ?node_26279.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26281 (s : N.State) (i : N.Inputs) :
  R.v26281 (state s) (inputs i) = Zmod.unsigned (N.v26281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26281 s i)) at 1.
  unfold R.v26281, N.v26281.
  rewrite ?node_9998.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26282 (s : N.State) (i : N.Inputs) :
  R.v26282 (state s) (inputs i) = Zmod.unsigned (N.v26282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26282 s i)) at 1.
  unfold R.v26282, N.v26282.
  unfold R.v6, N.v6.
  rewrite ?node_10214.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26283 (s : N.State) (i : N.Inputs) :
  R.v26283 (state s) (inputs i) = Zmod.unsigned (N.v26283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26283 s i)) at 1.
  unfold R.v26283, N.v26283.
  rewrite ?node_26281.
  rewrite ?node_26282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26284 (s : N.State) (i : N.Inputs) :
  R.v26284 (state s) (inputs i) = Zmod.unsigned (N.v26284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26284 s i)) at 1.
  unfold R.v26284, N.v26284.
  rewrite ?node_26280.
  rewrite ?node_26283.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26285 (s : N.State) (i : N.Inputs) :
  R.v26285 (state s) (inputs i) = Zmod.unsigned (N.v26285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26285 s i)) at 1.
  unfold R.v26285, N.v26285.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26286 (s : N.State) (i : N.Inputs) :
  R.v26286 (state s) (inputs i) = Zmod.unsigned (N.v26286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26286 s i)) at 1.
  unfold R.v26286, N.v26286.
  rewrite ?node_10009.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26287 (s : N.State) (i : N.Inputs) :
  R.v26287 (state s) (inputs i) = Zmod.unsigned (N.v26287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26287 s i)) at 1.
  unfold R.v26287, N.v26287.
  unfold R.v16463, N.v16463.
  rewrite !state_r1073_nr_5F1073.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1073_nr_5F1073 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26288 (s : N.State) (i : N.Inputs) :
  R.v26288 (state s) (inputs i) = Zmod.unsigned (N.v26288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26288 s i)) at 1.
  unfold R.v26288, N.v26288.
  unfold R.v16463, N.v16463.
  rewrite !state_r1072_nr_5F1072.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1072_nr_5F1072 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26289 (s : N.State) (i : N.Inputs) :
  R.v26289 (state s) (inputs i) = Zmod.unsigned (N.v26289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26289 s i)) at 1.
  unfold R.v26289, N.v26289.
  unfold R.v6, N.v6.
  rewrite !state_r1071_nr_5F1071.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1071_nr_5F1071 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26290 (s : N.State) (i : N.Inputs) :
  R.v26290 (state s) (inputs i) = Zmod.unsigned (N.v26290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26290 s i)) at 1.
  unfold R.v26290, N.v26290.
  unfold R.v6, N.v6.
  rewrite !state_r1070_nr_5F1070.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1070_nr_5F1070 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26291 (s : N.State) (i : N.Inputs) :
  R.v26291 (state s) (inputs i) = Zmod.unsigned (N.v26291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26291 s i)) at 1.
  unfold R.v26291, N.v26291.
  rewrite ?node_26289.
  rewrite ?node_26290.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26292 (s : N.State) (i : N.Inputs) :
  R.v26292 (state s) (inputs i) = Zmod.unsigned (N.v26292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26292 s i)) at 1.
  unfold R.v26292, N.v26292.
  unfold R.v16484, N.v16484.
  rewrite ?node_26291.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26293 (s : N.State) (i : N.Inputs) :
  R.v26293 (state s) (inputs i) = Zmod.unsigned (N.v26293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26293 s i)) at 1.
  unfold R.v26293, N.v26293.
  rewrite ?node_26286.
  rewrite ?node_26287.
  rewrite ?node_26288.
  rewrite ?node_26292.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26294 (s : N.State) (i : N.Inputs) :
  R.v26294 (state s) (inputs i) = Zmod.unsigned (N.v26294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26294 s i)) at 1.
  unfold R.v26294, N.v26294.
  unfold R.v6, N.v6.
  rewrite ?node_26293.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26295 (s : N.State) (i : N.Inputs) :
  R.v26295 (state s) (inputs i) = Zmod.unsigned (N.v26295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26295 s i)) at 1.
  unfold R.v26295, N.v26295.
  rewrite ?node_10010.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26296 (s : N.State) (i : N.Inputs) :
  R.v26296 (state s) (inputs i) = Zmod.unsigned (N.v26296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26296 s i)) at 1.
  unfold R.v26296, N.v26296.
  unfold R.v6, N.v6.
  rewrite ?node_10164.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26297 (s : N.State) (i : N.Inputs) :
  R.v26297 (state s) (inputs i) = Zmod.unsigned (N.v26297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26297 s i)) at 1.
  unfold R.v26297, N.v26297.
  unfold R.v6, N.v6.
  rewrite ?node_10217.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26298 (s : N.State) (i : N.Inputs) :
  R.v26298 (state s) (inputs i) = Zmod.unsigned (N.v26298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26298 s i)) at 1.
  unfold R.v26298, N.v26298.
  rewrite ?node_26295.
  rewrite ?node_26296.
  rewrite ?node_26297.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26299 (s : N.State) (i : N.Inputs) :
  R.v26299 (state s) (inputs i) = Zmod.unsigned (N.v26299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26299 s i)) at 1.
  unfold R.v26299, N.v26299.
  rewrite ?node_26294.
  rewrite ?node_26298.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26300 (s : N.State) (i : N.Inputs) :
  R.v26300 (state s) (inputs i) = Zmod.unsigned (N.v26300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26300 s i)) at 1.
  unfold R.v26300, N.v26300.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26301 (s : N.State) (i : N.Inputs) :
  R.v26301 (state s) (inputs i) = Zmod.unsigned (N.v26301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26301 s i)) at 1.
  unfold R.v26301, N.v26301.
  unfold R.v16463, N.v16463.
  rewrite !state_r1072_nr_5F1072.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1072_nr_5F1072 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26302 (s : N.State) (i : N.Inputs) :
  R.v26302 (state s) (inputs i) = Zmod.unsigned (N.v26302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26302 s i)) at 1.
  unfold R.v26302, N.v26302.
  unfold R.v6, N.v6.
  rewrite !state_r1071_nr_5F1071.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1071_nr_5F1071 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26303 (s : N.State) (i : N.Inputs) :
  R.v26303 (state s) (inputs i) = Zmod.unsigned (N.v26303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26303 s i)) at 1.
  unfold R.v26303, N.v26303.
  unfold R.v6, N.v6.
  rewrite !state_r1070_nr_5F1070.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1070_nr_5F1070 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26304 (s : N.State) (i : N.Inputs) :
  R.v26304 (state s) (inputs i) = Zmod.unsigned (N.v26304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26304 s i)) at 1.
  unfold R.v26304, N.v26304.
  rewrite ?node_26302.
  rewrite ?node_26303.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26305 (s : N.State) (i : N.Inputs) :
  R.v26305 (state s) (inputs i) = Zmod.unsigned (N.v26305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26305 s i)) at 1.
  unfold R.v26305, N.v26305.
  unfold R.v16484, N.v16484.
  rewrite ?node_26304.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26306 (s : N.State) (i : N.Inputs) :
  R.v26306 (state s) (inputs i) = Zmod.unsigned (N.v26306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26306 s i)) at 1.
  unfold R.v26306, N.v26306.
  rewrite ?node_26301.
  rewrite ?node_26305.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26307 (s : N.State) (i : N.Inputs) :
  R.v26307 (state s) (inputs i) = Zmod.unsigned (N.v26307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26307 s i)) at 1.
  unfold R.v26307, N.v26307.
  unfold R.v6, N.v6.
  rewrite ?node_26306.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26308 (s : N.State) (i : N.Inputs) :
  R.v26308 (state s) (inputs i) = Zmod.unsigned (N.v26308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26308 s i)) at 1.
  unfold R.v26308, N.v26308.
  rewrite ?node_10005.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26309 (s : N.State) (i : N.Inputs) :
  R.v26309 (state s) (inputs i) = Zmod.unsigned (N.v26309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26309 s i)) at 1.
  unfold R.v26309, N.v26309.
  unfold R.v6, N.v6.
  rewrite ?node_10164.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26310 (s : N.State) (i : N.Inputs) :
  R.v26310 (state s) (inputs i) = Zmod.unsigned (N.v26310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26310 s i)) at 1.
  unfold R.v26310, N.v26310.
  rewrite ?node_26308.
  rewrite ?node_26309.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26311 (s : N.State) (i : N.Inputs) :
  R.v26311 (state s) (inputs i) = Zmod.unsigned (N.v26311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26311 s i)) at 1.
  unfold R.v26311, N.v26311.
  rewrite ?node_26307.
  rewrite ?node_26310.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26312 (s : N.State) (i : N.Inputs) :
  R.v26312 (state s) (inputs i) = Zmod.unsigned (N.v26312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26312 s i)) at 1.
  unfold R.v26312, N.v26312.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26313 (s : N.State) (i : N.Inputs) :
  R.v26313 (state s) (inputs i) = Zmod.unsigned (N.v26313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26313 s i)) at 1.
  unfold R.v26313, N.v26313.
  rewrite ?node_10009.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26314 (s : N.State) (i : N.Inputs) :
  R.v26314 (state s) (inputs i) = Zmod.unsigned (N.v26314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26314 s i)) at 1.
  unfold R.v26314, N.v26314.
  unfold R.v6, N.v6.
  rewrite !state_r1073_nr_5F1073.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1073_nr_5F1073 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26315 (s : N.State) (i : N.Inputs) :
  R.v26315 (state s) (inputs i) = Zmod.unsigned (N.v26315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26315 s i)) at 1.
  unfold R.v26315, N.v26315.
  unfold R.v6, N.v6.
  rewrite ?node_10005.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26316 (s : N.State) (i : N.Inputs) :
  R.v26316 (state s) (inputs i) = Zmod.unsigned (N.v26316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26316 s i)) at 1.
  unfold R.v26316, N.v26316.
  rewrite ?node_26314.
  rewrite ?node_26315.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26317 (s : N.State) (i : N.Inputs) :
  R.v26317 (state s) (inputs i) = Zmod.unsigned (N.v26317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26317 s i)) at 1.
  unfold R.v26317, N.v26317.
  unfold R.v16484, N.v16484.
  rewrite ?node_26316.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26318 (s : N.State) (i : N.Inputs) :
  R.v26318 (state s) (inputs i) = Zmod.unsigned (N.v26318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26318 s i)) at 1.
  unfold R.v26318, N.v26318.
  rewrite ?node_26313.
  rewrite ?node_26317.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26319 (s : N.State) (i : N.Inputs) :
  R.v26319 (state s) (inputs i) = Zmod.unsigned (N.v26319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26319 s i)) at 1.
  unfold R.v26319, N.v26319.
  unfold R.v6, N.v6.
  rewrite ?node_26318.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26320 (s : N.State) (i : N.Inputs) :
  R.v26320 (state s) (inputs i) = Zmod.unsigned (N.v26320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26320 s i)) at 1.
  unfold R.v26320, N.v26320.
  rewrite ?node_10010.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26321 (s : N.State) (i : N.Inputs) :
  R.v26321 (state s) (inputs i) = Zmod.unsigned (N.v26321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26321 s i)) at 1.
  unfold R.v26321, N.v26321.
  unfold R.v6, N.v6.
  rewrite ?node_10217.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26322 (s : N.State) (i : N.Inputs) :
  R.v26322 (state s) (inputs i) = Zmod.unsigned (N.v26322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26322 s i)) at 1.
  unfold R.v26322, N.v26322.
  rewrite ?node_26320.
  rewrite ?node_26321.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26323 (s : N.State) (i : N.Inputs) :
  R.v26323 (state s) (inputs i) = Zmod.unsigned (N.v26323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26323 s i)) at 1.
  unfold R.v26323, N.v26323.
  rewrite ?node_26319.
  rewrite ?node_26322.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26324 (s : N.State) (i : N.Inputs) :
  R.v26324 (state s) (inputs i) = Zmod.unsigned (N.v26324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26324 s i)) at 1.
  unfold R.v26324, N.v26324.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26325 (s : N.State) (i : N.Inputs) :
  R.v26325 (state s) (inputs i) = Zmod.unsigned (N.v26325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26325 s i)) at 1.
  unfold R.v26325, N.v26325.
  rewrite ?node_10016.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26326 (s : N.State) (i : N.Inputs) :
  R.v26326 (state s) (inputs i) = Zmod.unsigned (N.v26326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26326 s i)) at 1.
  unfold R.v26326, N.v26326.
  unfold R.v16463, N.v16463.
  rewrite !state_r1077_nr_5F1077.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1077_nr_5F1077 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26327 (s : N.State) (i : N.Inputs) :
  R.v26327 (state s) (inputs i) = Zmod.unsigned (N.v26327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26327 s i)) at 1.
  unfold R.v26327, N.v26327.
  unfold R.v16463, N.v16463.
  rewrite !state_r1076_nr_5F1076.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1076_nr_5F1076 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26328 (s : N.State) (i : N.Inputs) :
  R.v26328 (state s) (inputs i) = Zmod.unsigned (N.v26328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26328 s i)) at 1.
  unfold R.v26328, N.v26328.
  unfold R.v6, N.v6.
  rewrite !state_r1075_nr_5F1075.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1075_nr_5F1075 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26329 (s : N.State) (i : N.Inputs) :
  R.v26329 (state s) (inputs i) = Zmod.unsigned (N.v26329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26329 s i)) at 1.
  unfold R.v26329, N.v26329.
  unfold R.v6, N.v6.
  rewrite !state_r1074_nr_5F1074.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1074_nr_5F1074 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26330 (s : N.State) (i : N.Inputs) :
  R.v26330 (state s) (inputs i) = Zmod.unsigned (N.v26330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26330 s i)) at 1.
  unfold R.v26330, N.v26330.
  rewrite ?node_26328.
  rewrite ?node_26329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26331 (s : N.State) (i : N.Inputs) :
  R.v26331 (state s) (inputs i) = Zmod.unsigned (N.v26331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26331 s i)) at 1.
  unfold R.v26331, N.v26331.
  unfold R.v16484, N.v16484.
  rewrite ?node_26330.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26332 (s : N.State) (i : N.Inputs) :
  R.v26332 (state s) (inputs i) = Zmod.unsigned (N.v26332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26332 s i)) at 1.
  unfold R.v26332, N.v26332.
  rewrite ?node_26325.
  rewrite ?node_26326.
  rewrite ?node_26327.
  rewrite ?node_26331.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26333 (s : N.State) (i : N.Inputs) :
  R.v26333 (state s) (inputs i) = Zmod.unsigned (N.v26333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26333 s i)) at 1.
  unfold R.v26333, N.v26333.
  unfold R.v6, N.v6.
  rewrite ?node_26332.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26334 (s : N.State) (i : N.Inputs) :
  R.v26334 (state s) (inputs i) = Zmod.unsigned (N.v26334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26334 s i)) at 1.
  unfold R.v26334, N.v26334.
  rewrite ?node_10017.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26335 (s : N.State) (i : N.Inputs) :
  R.v26335 (state s) (inputs i) = Zmod.unsigned (N.v26335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26335 s i)) at 1.
  unfold R.v26335, N.v26335.
  unfold R.v6, N.v6.
  rewrite ?node_10171.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26336 (s : N.State) (i : N.Inputs) :
  R.v26336 (state s) (inputs i) = Zmod.unsigned (N.v26336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26336 s i)) at 1.
  unfold R.v26336, N.v26336.
  unfold R.v6, N.v6.
  rewrite ?node_10221.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26337 (s : N.State) (i : N.Inputs) :
  R.v26337 (state s) (inputs i) = Zmod.unsigned (N.v26337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26337 s i)) at 1.
  unfold R.v26337, N.v26337.
  rewrite ?node_26334.
  rewrite ?node_26335.
  rewrite ?node_26336.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26338 (s : N.State) (i : N.Inputs) :
  R.v26338 (state s) (inputs i) = Zmod.unsigned (N.v26338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26338 s i)) at 1.
  unfold R.v26338, N.v26338.
  rewrite ?node_26333.
  rewrite ?node_26337.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26339 (s : N.State) (i : N.Inputs) :
  R.v26339 (state s) (inputs i) = Zmod.unsigned (N.v26339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26339 s i)) at 1.
  unfold R.v26339, N.v26339.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26340 (s : N.State) (i : N.Inputs) :
  R.v26340 (state s) (inputs i) = Zmod.unsigned (N.v26340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26340 s i)) at 1.
  unfold R.v26340, N.v26340.
  unfold R.v16463, N.v16463.
  rewrite !state_r1076_nr_5F1076.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1076_nr_5F1076 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26341 (s : N.State) (i : N.Inputs) :
  R.v26341 (state s) (inputs i) = Zmod.unsigned (N.v26341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26341 s i)) at 1.
  unfold R.v26341, N.v26341.
  unfold R.v6, N.v6.
  rewrite !state_r1075_nr_5F1075.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1075_nr_5F1075 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26342 (s : N.State) (i : N.Inputs) :
  R.v26342 (state s) (inputs i) = Zmod.unsigned (N.v26342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26342 s i)) at 1.
  unfold R.v26342, N.v26342.
  unfold R.v6, N.v6.
  rewrite !state_r1074_nr_5F1074.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1074_nr_5F1074 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26343 (s : N.State) (i : N.Inputs) :
  R.v26343 (state s) (inputs i) = Zmod.unsigned (N.v26343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26343 s i)) at 1.
  unfold R.v26343, N.v26343.
  rewrite ?node_26341.
  rewrite ?node_26342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26344 (s : N.State) (i : N.Inputs) :
  R.v26344 (state s) (inputs i) = Zmod.unsigned (N.v26344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26344 s i)) at 1.
  unfold R.v26344, N.v26344.
  unfold R.v16484, N.v16484.
  rewrite ?node_26343.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26345 (s : N.State) (i : N.Inputs) :
  R.v26345 (state s) (inputs i) = Zmod.unsigned (N.v26345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26345 s i)) at 1.
  unfold R.v26345, N.v26345.
  rewrite ?node_26340.
  rewrite ?node_26344.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26346 (s : N.State) (i : N.Inputs) :
  R.v26346 (state s) (inputs i) = Zmod.unsigned (N.v26346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26346 s i)) at 1.
  unfold R.v26346, N.v26346.
  unfold R.v6, N.v6.
  rewrite ?node_26345.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26347 (s : N.State) (i : N.Inputs) :
  R.v26347 (state s) (inputs i) = Zmod.unsigned (N.v26347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26347 s i)) at 1.
  unfold R.v26347, N.v26347.
  rewrite ?node_10012.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26348 (s : N.State) (i : N.Inputs) :
  R.v26348 (state s) (inputs i) = Zmod.unsigned (N.v26348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26348 s i)) at 1.
  unfold R.v26348, N.v26348.
  unfold R.v6, N.v6.
  rewrite ?node_10171.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26349 (s : N.State) (i : N.Inputs) :
  R.v26349 (state s) (inputs i) = Zmod.unsigned (N.v26349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26349 s i)) at 1.
  unfold R.v26349, N.v26349.
  rewrite ?node_26347.
  rewrite ?node_26348.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26350 (s : N.State) (i : N.Inputs) :
  R.v26350 (state s) (inputs i) = Zmod.unsigned (N.v26350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26350 s i)) at 1.
  unfold R.v26350, N.v26350.
  rewrite ?node_26346.
  rewrite ?node_26349.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26351 (s : N.State) (i : N.Inputs) :
  R.v26351 (state s) (inputs i) = Zmod.unsigned (N.v26351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26351 s i)) at 1.
  unfold R.v26351, N.v26351.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26352 (s : N.State) (i : N.Inputs) :
  R.v26352 (state s) (inputs i) = Zmod.unsigned (N.v26352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26352 s i)) at 1.
  unfold R.v26352, N.v26352.
  rewrite ?node_10016.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26353 (s : N.State) (i : N.Inputs) :
  R.v26353 (state s) (inputs i) = Zmod.unsigned (N.v26353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26353 s i)) at 1.
  unfold R.v26353, N.v26353.
  unfold R.v6, N.v6.
  rewrite !state_r1077_nr_5F1077.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1077_nr_5F1077 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26354 (s : N.State) (i : N.Inputs) :
  R.v26354 (state s) (inputs i) = Zmod.unsigned (N.v26354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26354 s i)) at 1.
  unfold R.v26354, N.v26354.
  unfold R.v6, N.v6.
  rewrite ?node_10012.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26355 (s : N.State) (i : N.Inputs) :
  R.v26355 (state s) (inputs i) = Zmod.unsigned (N.v26355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26355 s i)) at 1.
  unfold R.v26355, N.v26355.
  rewrite ?node_26353.
  rewrite ?node_26354.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26356 (s : N.State) (i : N.Inputs) :
  R.v26356 (state s) (inputs i) = Zmod.unsigned (N.v26356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26356 s i)) at 1.
  unfold R.v26356, N.v26356.
  unfold R.v16484, N.v16484.
  rewrite ?node_26355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26357 (s : N.State) (i : N.Inputs) :
  R.v26357 (state s) (inputs i) = Zmod.unsigned (N.v26357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26357 s i)) at 1.
  unfold R.v26357, N.v26357.
  rewrite ?node_26352.
  rewrite ?node_26356.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26358 (s : N.State) (i : N.Inputs) :
  R.v26358 (state s) (inputs i) = Zmod.unsigned (N.v26358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26358 s i)) at 1.
  unfold R.v26358, N.v26358.
  unfold R.v6, N.v6.
  rewrite ?node_26357.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26359 (s : N.State) (i : N.Inputs) :
  R.v26359 (state s) (inputs i) = Zmod.unsigned (N.v26359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26359 s i)) at 1.
  unfold R.v26359, N.v26359.
  rewrite ?node_10017.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26360 (s : N.State) (i : N.Inputs) :
  R.v26360 (state s) (inputs i) = Zmod.unsigned (N.v26360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26360 s i)) at 1.
  unfold R.v26360, N.v26360.
  unfold R.v6, N.v6.
  rewrite ?node_10221.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26361 (s : N.State) (i : N.Inputs) :
  R.v26361 (state s) (inputs i) = Zmod.unsigned (N.v26361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26361 s i)) at 1.
  unfold R.v26361, N.v26361.
  rewrite ?node_26359.
  rewrite ?node_26360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26362 (s : N.State) (i : N.Inputs) :
  R.v26362 (state s) (inputs i) = Zmod.unsigned (N.v26362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26362 s i)) at 1.
  unfold R.v26362, N.v26362.
  rewrite ?node_26358.
  rewrite ?node_26361.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26363 (s : N.State) (i : N.Inputs) :
  R.v26363 (state s) (inputs i) = Zmod.unsigned (N.v26363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26363 s i)) at 1.
  unfold R.v26363, N.v26363.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26364 (s : N.State) (i : N.Inputs) :
  R.v26364 (state s) (inputs i) = Zmod.unsigned (N.v26364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26364 s i)) at 1.
  unfold R.v26364, N.v26364.
  rewrite ?node_10024.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26365 (s : N.State) (i : N.Inputs) :
  R.v26365 (state s) (inputs i) = Zmod.unsigned (N.v26365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26365 s i)) at 1.
  unfold R.v26365, N.v26365.
  unfold R.v16463, N.v16463.
  rewrite !state_r1081_nr_5F1081.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1081_nr_5F1081 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26366 (s : N.State) (i : N.Inputs) :
  R.v26366 (state s) (inputs i) = Zmod.unsigned (N.v26366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26366 s i)) at 1.
  unfold R.v26366, N.v26366.
  unfold R.v16463, N.v16463.
  rewrite !state_r1080_nr_5F1080.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1080_nr_5F1080 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26367 (s : N.State) (i : N.Inputs) :
  R.v26367 (state s) (inputs i) = Zmod.unsigned (N.v26367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26367 s i)) at 1.
  unfold R.v26367, N.v26367.
  unfold R.v6, N.v6.
  rewrite !state_r1079_nr_5F1079.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1079_nr_5F1079 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26368 (s : N.State) (i : N.Inputs) :
  R.v26368 (state s) (inputs i) = Zmod.unsigned (N.v26368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26368 s i)) at 1.
  unfold R.v26368, N.v26368.
  unfold R.v6, N.v6.
  rewrite !state_r1078_nr_5F1078.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1078_nr_5F1078 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26369 (s : N.State) (i : N.Inputs) :
  R.v26369 (state s) (inputs i) = Zmod.unsigned (N.v26369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26369 s i)) at 1.
  unfold R.v26369, N.v26369.
  rewrite ?node_26367.
  rewrite ?node_26368.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26370 (s : N.State) (i : N.Inputs) :
  R.v26370 (state s) (inputs i) = Zmod.unsigned (N.v26370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26370 s i)) at 1.
  unfold R.v26370, N.v26370.
  unfold R.v16484, N.v16484.
  rewrite ?node_26369.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26371 (s : N.State) (i : N.Inputs) :
  R.v26371 (state s) (inputs i) = Zmod.unsigned (N.v26371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26371 s i)) at 1.
  unfold R.v26371, N.v26371.
  rewrite ?node_26364.
  rewrite ?node_26365.
  rewrite ?node_26366.
  rewrite ?node_26370.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26372 (s : N.State) (i : N.Inputs) :
  R.v26372 (state s) (inputs i) = Zmod.unsigned (N.v26372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26372 s i)) at 1.
  unfold R.v26372, N.v26372.
  unfold R.v6, N.v6.
  rewrite ?node_26371.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26373 (s : N.State) (i : N.Inputs) :
  R.v26373 (state s) (inputs i) = Zmod.unsigned (N.v26373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26373 s i)) at 1.
  unfold R.v26373, N.v26373.
  rewrite ?node_10025.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26374 (s : N.State) (i : N.Inputs) :
  R.v26374 (state s) (inputs i) = Zmod.unsigned (N.v26374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26374 s i)) at 1.
  unfold R.v26374, N.v26374.
  unfold R.v6, N.v6.
  rewrite ?node_10179.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26375 (s : N.State) (i : N.Inputs) :
  R.v26375 (state s) (inputs i) = Zmod.unsigned (N.v26375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26375 s i)) at 1.
  unfold R.v26375, N.v26375.
  unfold R.v6, N.v6.
  rewrite ?node_10225.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26376 (s : N.State) (i : N.Inputs) :
  R.v26376 (state s) (inputs i) = Zmod.unsigned (N.v26376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26376 s i)) at 1.
  unfold R.v26376, N.v26376.
  rewrite ?node_26373.
  rewrite ?node_26374.
  rewrite ?node_26375.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26377 (s : N.State) (i : N.Inputs) :
  R.v26377 (state s) (inputs i) = Zmod.unsigned (N.v26377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26377 s i)) at 1.
  unfold R.v26377, N.v26377.
  rewrite ?node_26372.
  rewrite ?node_26376.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26378 (s : N.State) (i : N.Inputs) :
  R.v26378 (state s) (inputs i) = Zmod.unsigned (N.v26378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26378 s i)) at 1.
  unfold R.v26378, N.v26378.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26379 (s : N.State) (i : N.Inputs) :
  R.v26379 (state s) (inputs i) = Zmod.unsigned (N.v26379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26379 s i)) at 1.
  unfold R.v26379, N.v26379.
  unfold R.v16463, N.v16463.
  rewrite !state_r1080_nr_5F1080.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1080_nr_5F1080 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26380 (s : N.State) (i : N.Inputs) :
  R.v26380 (state s) (inputs i) = Zmod.unsigned (N.v26380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26380 s i)) at 1.
  unfold R.v26380, N.v26380.
  unfold R.v6, N.v6.
  rewrite !state_r1079_nr_5F1079.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1079_nr_5F1079 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26381 (s : N.State) (i : N.Inputs) :
  R.v26381 (state s) (inputs i) = Zmod.unsigned (N.v26381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26381 s i)) at 1.
  unfold R.v26381, N.v26381.
  unfold R.v6, N.v6.
  rewrite !state_r1078_nr_5F1078.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1078_nr_5F1078 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26382 (s : N.State) (i : N.Inputs) :
  R.v26382 (state s) (inputs i) = Zmod.unsigned (N.v26382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26382 s i)) at 1.
  unfold R.v26382, N.v26382.
  rewrite ?node_26380.
  rewrite ?node_26381.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26383 (s : N.State) (i : N.Inputs) :
  R.v26383 (state s) (inputs i) = Zmod.unsigned (N.v26383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26383 s i)) at 1.
  unfold R.v26383, N.v26383.
  unfold R.v16484, N.v16484.
  rewrite ?node_26382.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26384 (s : N.State) (i : N.Inputs) :
  R.v26384 (state s) (inputs i) = Zmod.unsigned (N.v26384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26384 s i)) at 1.
  unfold R.v26384, N.v26384.
  rewrite ?node_26379.
  rewrite ?node_26383.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26385 (s : N.State) (i : N.Inputs) :
  R.v26385 (state s) (inputs i) = Zmod.unsigned (N.v26385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26385 s i)) at 1.
  unfold R.v26385, N.v26385.
  unfold R.v6, N.v6.
  rewrite ?node_26384.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26386 (s : N.State) (i : N.Inputs) :
  R.v26386 (state s) (inputs i) = Zmod.unsigned (N.v26386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26386 s i)) at 1.
  unfold R.v26386, N.v26386.
  rewrite ?node_10020.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26387 (s : N.State) (i : N.Inputs) :
  R.v26387 (state s) (inputs i) = Zmod.unsigned (N.v26387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26387 s i)) at 1.
  unfold R.v26387, N.v26387.
  unfold R.v6, N.v6.
  rewrite ?node_10179.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26388 (s : N.State) (i : N.Inputs) :
  R.v26388 (state s) (inputs i) = Zmod.unsigned (N.v26388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26388 s i)) at 1.
  unfold R.v26388, N.v26388.
  rewrite ?node_26386.
  rewrite ?node_26387.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26389 (s : N.State) (i : N.Inputs) :
  R.v26389 (state s) (inputs i) = Zmod.unsigned (N.v26389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26389 s i)) at 1.
  unfold R.v26389, N.v26389.
  rewrite ?node_26385.
  rewrite ?node_26388.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26390 (s : N.State) (i : N.Inputs) :
  R.v26390 (state s) (inputs i) = Zmod.unsigned (N.v26390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26390 s i)) at 1.
  unfold R.v26390, N.v26390.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26391 (s : N.State) (i : N.Inputs) :
  R.v26391 (state s) (inputs i) = Zmod.unsigned (N.v26391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26391 s i)) at 1.
  unfold R.v26391, N.v26391.
  rewrite ?node_10024.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26392 (s : N.State) (i : N.Inputs) :
  R.v26392 (state s) (inputs i) = Zmod.unsigned (N.v26392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26392 s i)) at 1.
  unfold R.v26392, N.v26392.
  unfold R.v6, N.v6.
  rewrite !state_r1081_nr_5F1081.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1081_nr_5F1081 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26393 (s : N.State) (i : N.Inputs) :
  R.v26393 (state s) (inputs i) = Zmod.unsigned (N.v26393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26393 s i)) at 1.
  unfold R.v26393, N.v26393.
  unfold R.v6, N.v6.
  rewrite ?node_10020.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26394 (s : N.State) (i : N.Inputs) :
  R.v26394 (state s) (inputs i) = Zmod.unsigned (N.v26394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26394 s i)) at 1.
  unfold R.v26394, N.v26394.
  rewrite ?node_26392.
  rewrite ?node_26393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26395 (s : N.State) (i : N.Inputs) :
  R.v26395 (state s) (inputs i) = Zmod.unsigned (N.v26395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26395 s i)) at 1.
  unfold R.v26395, N.v26395.
  unfold R.v16484, N.v16484.
  rewrite ?node_26394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26396 (s : N.State) (i : N.Inputs) :
  R.v26396 (state s) (inputs i) = Zmod.unsigned (N.v26396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26396 s i)) at 1.
  unfold R.v26396, N.v26396.
  rewrite ?node_26391.
  rewrite ?node_26395.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26397 (s : N.State) (i : N.Inputs) :
  R.v26397 (state s) (inputs i) = Zmod.unsigned (N.v26397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26397 s i)) at 1.
  unfold R.v26397, N.v26397.
  unfold R.v6, N.v6.
  rewrite ?node_26396.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26398 (s : N.State) (i : N.Inputs) :
  R.v26398 (state s) (inputs i) = Zmod.unsigned (N.v26398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26398 s i)) at 1.
  unfold R.v26398, N.v26398.
  rewrite ?node_10025.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26399 (s : N.State) (i : N.Inputs) :
  R.v26399 (state s) (inputs i) = Zmod.unsigned (N.v26399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26399 s i)) at 1.
  unfold R.v26399, N.v26399.
  unfold R.v6, N.v6.
  rewrite ?node_10225.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26400 (s : N.State) (i : N.Inputs) :
  R.v26400 (state s) (inputs i) = Zmod.unsigned (N.v26400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26400 s i)) at 1.
  unfold R.v26400, N.v26400.
  rewrite ?node_26398.
  rewrite ?node_26399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26401 (s : N.State) (i : N.Inputs) :
  R.v26401 (state s) (inputs i) = Zmod.unsigned (N.v26401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26401 s i)) at 1.
  unfold R.v26401, N.v26401.
  rewrite ?node_26397.
  rewrite ?node_26400.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26402 (s : N.State) (i : N.Inputs) :
  R.v26402 (state s) (inputs i) = Zmod.unsigned (N.v26402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26402 s i)) at 1.
  unfold R.v26402, N.v26402.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26403 (s : N.State) (i : N.Inputs) :
  R.v26403 (state s) (inputs i) = Zmod.unsigned (N.v26403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26403 s i)) at 1.
  unfold R.v26403, N.v26403.
  rewrite ?node_10032.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26404 (s : N.State) (i : N.Inputs) :
  R.v26404 (state s) (inputs i) = Zmod.unsigned (N.v26404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26404 s i)) at 1.
  unfold R.v26404, N.v26404.
  unfold R.v16463, N.v16463.
  rewrite !state_r1085_nr_5F1085.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1085_nr_5F1085 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26405 (s : N.State) (i : N.Inputs) :
  R.v26405 (state s) (inputs i) = Zmod.unsigned (N.v26405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26405 s i)) at 1.
  unfold R.v26405, N.v26405.
  unfold R.v16463, N.v16463.
  rewrite !state_r1084_nr_5F1084.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1084_nr_5F1084 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26406 (s : N.State) (i : N.Inputs) :
  R.v26406 (state s) (inputs i) = Zmod.unsigned (N.v26406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26406 s i)) at 1.
  unfold R.v26406, N.v26406.
  unfold R.v6, N.v6.
  rewrite !state_r1083_nr_5F1083.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1083_nr_5F1083 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26407 (s : N.State) (i : N.Inputs) :
  R.v26407 (state s) (inputs i) = Zmod.unsigned (N.v26407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26407 s i)) at 1.
  unfold R.v26407, N.v26407.
  unfold R.v6, N.v6.
  rewrite !state_r1082_nr_5F1082.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1082_nr_5F1082 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26408 (s : N.State) (i : N.Inputs) :
  R.v26408 (state s) (inputs i) = Zmod.unsigned (N.v26408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26408 s i)) at 1.
  unfold R.v26408, N.v26408.
  rewrite ?node_26406.
  rewrite ?node_26407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26409 (s : N.State) (i : N.Inputs) :
  R.v26409 (state s) (inputs i) = Zmod.unsigned (N.v26409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26409 s i)) at 1.
  unfold R.v26409, N.v26409.
  unfold R.v16484, N.v16484.
  rewrite ?node_26408.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26410 (s : N.State) (i : N.Inputs) :
  R.v26410 (state s) (inputs i) = Zmod.unsigned (N.v26410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26410 s i)) at 1.
  unfold R.v26410, N.v26410.
  rewrite ?node_26403.
  rewrite ?node_26404.
  rewrite ?node_26405.
  rewrite ?node_26409.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26411 (s : N.State) (i : N.Inputs) :
  R.v26411 (state s) (inputs i) = Zmod.unsigned (N.v26411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26411 s i)) at 1.
  unfold R.v26411, N.v26411.
  unfold R.v6, N.v6.
  rewrite ?node_26410.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26412 (s : N.State) (i : N.Inputs) :
  R.v26412 (state s) (inputs i) = Zmod.unsigned (N.v26412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26412 s i)) at 1.
  unfold R.v26412, N.v26412.
  rewrite ?node_10033.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26413 (s : N.State) (i : N.Inputs) :
  R.v26413 (state s) (inputs i) = Zmod.unsigned (N.v26413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26413 s i)) at 1.
  unfold R.v26413, N.v26413.
  unfold R.v6, N.v6.
  rewrite ?node_10187.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26414 (s : N.State) (i : N.Inputs) :
  R.v26414 (state s) (inputs i) = Zmod.unsigned (N.v26414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26414 s i)) at 1.
  unfold R.v26414, N.v26414.
  unfold R.v6, N.v6.
  rewrite ?node_10238.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26415 (s : N.State) (i : N.Inputs) :
  R.v26415 (state s) (inputs i) = Zmod.unsigned (N.v26415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26415 s i)) at 1.
  unfold R.v26415, N.v26415.
  rewrite ?node_26412.
  rewrite ?node_26413.
  rewrite ?node_26414.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26416 (s : N.State) (i : N.Inputs) :
  R.v26416 (state s) (inputs i) = Zmod.unsigned (N.v26416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26416 s i)) at 1.
  unfold R.v26416, N.v26416.
  rewrite ?node_26411.
  rewrite ?node_26415.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26417 (s : N.State) (i : N.Inputs) :
  R.v26417 (state s) (inputs i) = Zmod.unsigned (N.v26417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26417 s i)) at 1.
  unfold R.v26417, N.v26417.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26418 (s : N.State) (i : N.Inputs) :
  R.v26418 (state s) (inputs i) = Zmod.unsigned (N.v26418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26418 s i)) at 1.
  unfold R.v26418, N.v26418.
  unfold R.v16463, N.v16463.
  rewrite !state_r1084_nr_5F1084.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1084_nr_5F1084 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26419 (s : N.State) (i : N.Inputs) :
  R.v26419 (state s) (inputs i) = Zmod.unsigned (N.v26419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26419 s i)) at 1.
  unfold R.v26419, N.v26419.
  unfold R.v6, N.v6.
  rewrite !state_r1083_nr_5F1083.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1083_nr_5F1083 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26420 (s : N.State) (i : N.Inputs) :
  R.v26420 (state s) (inputs i) = Zmod.unsigned (N.v26420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26420 s i)) at 1.
  unfold R.v26420, N.v26420.
  unfold R.v6, N.v6.
  rewrite !state_r1082_nr_5F1082.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1082_nr_5F1082 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26421 (s : N.State) (i : N.Inputs) :
  R.v26421 (state s) (inputs i) = Zmod.unsigned (N.v26421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26421 s i)) at 1.
  unfold R.v26421, N.v26421.
  rewrite ?node_26419.
  rewrite ?node_26420.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26422 (s : N.State) (i : N.Inputs) :
  R.v26422 (state s) (inputs i) = Zmod.unsigned (N.v26422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26422 s i)) at 1.
  unfold R.v26422, N.v26422.
  unfold R.v16484, N.v16484.
  rewrite ?node_26421.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26423 (s : N.State) (i : N.Inputs) :
  R.v26423 (state s) (inputs i) = Zmod.unsigned (N.v26423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26423 s i)) at 1.
  unfold R.v26423, N.v26423.
  rewrite ?node_26418.
  rewrite ?node_26422.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26424 (s : N.State) (i : N.Inputs) :
  R.v26424 (state s) (inputs i) = Zmod.unsigned (N.v26424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26424 s i)) at 1.
  unfold R.v26424, N.v26424.
  unfold R.v6, N.v6.
  rewrite ?node_26423.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26425 (s : N.State) (i : N.Inputs) :
  R.v26425 (state s) (inputs i) = Zmod.unsigned (N.v26425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26425 s i)) at 1.
  unfold R.v26425, N.v26425.
  rewrite ?node_10028.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26426 (s : N.State) (i : N.Inputs) :
  R.v26426 (state s) (inputs i) = Zmod.unsigned (N.v26426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26426 s i)) at 1.
  unfold R.v26426, N.v26426.
  unfold R.v6, N.v6.
  rewrite ?node_10187.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26427 (s : N.State) (i : N.Inputs) :
  R.v26427 (state s) (inputs i) = Zmod.unsigned (N.v26427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26427 s i)) at 1.
  unfold R.v26427, N.v26427.
  rewrite ?node_26425.
  rewrite ?node_26426.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26428 (s : N.State) (i : N.Inputs) :
  R.v26428 (state s) (inputs i) = Zmod.unsigned (N.v26428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26428 s i)) at 1.
  unfold R.v26428, N.v26428.
  rewrite ?node_26424.
  rewrite ?node_26427.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26429 (s : N.State) (i : N.Inputs) :
  R.v26429 (state s) (inputs i) = Zmod.unsigned (N.v26429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26429 s i)) at 1.
  unfold R.v26429, N.v26429.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26430 (s : N.State) (i : N.Inputs) :
  R.v26430 (state s) (inputs i) = Zmod.unsigned (N.v26430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26430 s i)) at 1.
  unfold R.v26430, N.v26430.
  rewrite ?node_10032.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26431 (s : N.State) (i : N.Inputs) :
  R.v26431 (state s) (inputs i) = Zmod.unsigned (N.v26431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26431 s i)) at 1.
  unfold R.v26431, N.v26431.
  unfold R.v6, N.v6.
  rewrite !state_r1085_nr_5F1085.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1085_nr_5F1085 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26432 (s : N.State) (i : N.Inputs) :
  R.v26432 (state s) (inputs i) = Zmod.unsigned (N.v26432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26432 s i)) at 1.
  unfold R.v26432, N.v26432.
  unfold R.v6, N.v6.
  rewrite ?node_10028.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26433 (s : N.State) (i : N.Inputs) :
  R.v26433 (state s) (inputs i) = Zmod.unsigned (N.v26433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26433 s i)) at 1.
  unfold R.v26433, N.v26433.
  rewrite ?node_26431.
  rewrite ?node_26432.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26434 (s : N.State) (i : N.Inputs) :
  R.v26434 (state s) (inputs i) = Zmod.unsigned (N.v26434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26434 s i)) at 1.
  unfold R.v26434, N.v26434.
  unfold R.v16484, N.v16484.
  rewrite ?node_26433.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26435 (s : N.State) (i : N.Inputs) :
  R.v26435 (state s) (inputs i) = Zmod.unsigned (N.v26435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26435 s i)) at 1.
  unfold R.v26435, N.v26435.
  rewrite ?node_26430.
  rewrite ?node_26434.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26436 (s : N.State) (i : N.Inputs) :
  R.v26436 (state s) (inputs i) = Zmod.unsigned (N.v26436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26436 s i)) at 1.
  unfold R.v26436, N.v26436.
  unfold R.v6, N.v6.
  rewrite ?node_26435.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26437 (s : N.State) (i : N.Inputs) :
  R.v26437 (state s) (inputs i) = Zmod.unsigned (N.v26437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26437 s i)) at 1.
  unfold R.v26437, N.v26437.
  rewrite ?node_10033.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26438 (s : N.State) (i : N.Inputs) :
  R.v26438 (state s) (inputs i) = Zmod.unsigned (N.v26438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26438 s i)) at 1.
  unfold R.v26438, N.v26438.
  unfold R.v6, N.v6.
  rewrite ?node_10238.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26439 (s : N.State) (i : N.Inputs) :
  R.v26439 (state s) (inputs i) = Zmod.unsigned (N.v26439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26439 s i)) at 1.
  unfold R.v26439, N.v26439.
  rewrite ?node_26437.
  rewrite ?node_26438.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26440 (s : N.State) (i : N.Inputs) :
  R.v26440 (state s) (inputs i) = Zmod.unsigned (N.v26440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26440 s i)) at 1.
  unfold R.v26440, N.v26440.
  rewrite ?node_26436.
  rewrite ?node_26439.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26441 (s : N.State) (i : N.Inputs) :
  R.v26441 (state s) (inputs i) = Zmod.unsigned (N.v26441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26441 s i)) at 1.
  unfold R.v26441, N.v26441.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26442 (s : N.State) (i : N.Inputs) :
  R.v26442 (state s) (inputs i) = Zmod.unsigned (N.v26442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26442 s i)) at 1.
  unfold R.v26442, N.v26442.
  rewrite ?node_10129.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26443 (s : N.State) (i : N.Inputs) :
  R.v26443 (state s) (inputs i) = Zmod.unsigned (N.v26443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26443 s i)) at 1.
  unfold R.v26443, N.v26443.
  unfold R.v16463, N.v16463.
  rewrite !state_r1090_nr_5F1090.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1090_nr_5F1090 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26444 (s : N.State) (i : N.Inputs) :
  R.v26444 (state s) (inputs i) = Zmod.unsigned (N.v26444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26444 s i)) at 1.
  unfold R.v26444, N.v26444.
  unfold R.v16463, N.v16463.
  rewrite !state_r1089_nr_5F1089.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1089_nr_5F1089 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26445 (s : N.State) (i : N.Inputs) :
  R.v26445 (state s) (inputs i) = Zmod.unsigned (N.v26445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26445 s i)) at 1.
  unfold R.v26445, N.v26445.
  unfold R.v6, N.v6.
  rewrite !state_r1088_nr_5F1088.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1088_nr_5F1088 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26446 (s : N.State) (i : N.Inputs) :
  R.v26446 (state s) (inputs i) = Zmod.unsigned (N.v26446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26446 s i)) at 1.
  unfold R.v26446, N.v26446.
  unfold R.v6, N.v6.
  rewrite !state_r1087_nr_5F1087.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1087_nr_5F1087 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26447 (s : N.State) (i : N.Inputs) :
  R.v26447 (state s) (inputs i) = Zmod.unsigned (N.v26447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26447 s i)) at 1.
  unfold R.v26447, N.v26447.
  rewrite ?node_26445.
  rewrite ?node_26446.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26448 (s : N.State) (i : N.Inputs) :
  R.v26448 (state s) (inputs i) = Zmod.unsigned (N.v26448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26448 s i)) at 1.
  unfold R.v26448, N.v26448.
  unfold R.v16484, N.v16484.
  rewrite ?node_26447.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26449 (s : N.State) (i : N.Inputs) :
  R.v26449 (state s) (inputs i) = Zmod.unsigned (N.v26449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26449 s i)) at 1.
  unfold R.v26449, N.v26449.
  rewrite ?node_26442.
  rewrite ?node_26443.
  rewrite ?node_26444.
  rewrite ?node_26448.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26450 (s : N.State) (i : N.Inputs) :
  R.v26450 (state s) (inputs i) = Zmod.unsigned (N.v26450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26450 s i)) at 1.
  unfold R.v26450, N.v26450.
  unfold R.v6, N.v6.
  rewrite ?node_26449.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26451 (s : N.State) (i : N.Inputs) :
  R.v26451 (state s) (inputs i) = Zmod.unsigned (N.v26451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26451 s i)) at 1.
  unfold R.v26451, N.v26451.
  rewrite ?node_10130.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26452 (s : N.State) (i : N.Inputs) :
  R.v26452 (state s) (inputs i) = Zmod.unsigned (N.v26452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26452 s i)) at 1.
  unfold R.v26452, N.v26452.
  unfold R.v6, N.v6.
  rewrite ?node_10286.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26453 (s : N.State) (i : N.Inputs) :
  R.v26453 (state s) (inputs i) = Zmod.unsigned (N.v26453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26453 s i)) at 1.
  unfold R.v26453, N.v26453.
  unfold R.v6, N.v6.
  rewrite ?node_10355.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26454 (s : N.State) (i : N.Inputs) :
  R.v26454 (state s) (inputs i) = Zmod.unsigned (N.v26454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26454 s i)) at 1.
  unfold R.v26454, N.v26454.
  rewrite ?node_26451.
  rewrite ?node_26452.
  rewrite ?node_26453.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26455 (s : N.State) (i : N.Inputs) :
  R.v26455 (state s) (inputs i) = Zmod.unsigned (N.v26455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26455 s i)) at 1.
  unfold R.v26455, N.v26455.
  rewrite ?node_26450.
  rewrite ?node_26454.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26456 (s : N.State) (i : N.Inputs) :
  R.v26456 (state s) (inputs i) = Zmod.unsigned (N.v26456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26456 s i)) at 1.
  unfold R.v26456, N.v26456.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26457 (s : N.State) (i : N.Inputs) :
  R.v26457 (state s) (inputs i) = Zmod.unsigned (N.v26457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26457 s i)) at 1.
  unfold R.v26457, N.v26457.
  unfold R.v16463, N.v16463.
  rewrite !state_r1089_nr_5F1089.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1089_nr_5F1089 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26458 (s : N.State) (i : N.Inputs) :
  R.v26458 (state s) (inputs i) = Zmod.unsigned (N.v26458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26458 s i)) at 1.
  unfold R.v26458, N.v26458.
  unfold R.v6, N.v6.
  rewrite !state_r1088_nr_5F1088.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1088_nr_5F1088 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26459 (s : N.State) (i : N.Inputs) :
  R.v26459 (state s) (inputs i) = Zmod.unsigned (N.v26459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26459 s i)) at 1.
  unfold R.v26459, N.v26459.
  unfold R.v6, N.v6.
  rewrite !state_r1087_nr_5F1087.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1087_nr_5F1087 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26460 (s : N.State) (i : N.Inputs) :
  R.v26460 (state s) (inputs i) = Zmod.unsigned (N.v26460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26460 s i)) at 1.
  unfold R.v26460, N.v26460.
  rewrite ?node_26458.
  rewrite ?node_26459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26461 (s : N.State) (i : N.Inputs) :
  R.v26461 (state s) (inputs i) = Zmod.unsigned (N.v26461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26461 s i)) at 1.
  unfold R.v26461, N.v26461.
  unfold R.v16484, N.v16484.
  rewrite ?node_26460.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26462 (s : N.State) (i : N.Inputs) :
  R.v26462 (state s) (inputs i) = Zmod.unsigned (N.v26462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26462 s i)) at 1.
  unfold R.v26462, N.v26462.
  rewrite ?node_26457.
  rewrite ?node_26461.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26463 (s : N.State) (i : N.Inputs) :
  R.v26463 (state s) (inputs i) = Zmod.unsigned (N.v26463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26463 s i)) at 1.
  unfold R.v26463, N.v26463.
  unfold R.v6, N.v6.
  rewrite ?node_26462.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26464 (s : N.State) (i : N.Inputs) :
  R.v26464 (state s) (inputs i) = Zmod.unsigned (N.v26464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26464 s i)) at 1.
  unfold R.v26464, N.v26464.
  rewrite ?node_10125.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26465 (s : N.State) (i : N.Inputs) :
  R.v26465 (state s) (inputs i) = Zmod.unsigned (N.v26465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26465 s i)) at 1.
  unfold R.v26465, N.v26465.
  unfold R.v6, N.v6.
  rewrite ?node_10286.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26466 (s : N.State) (i : N.Inputs) :
  R.v26466 (state s) (inputs i) = Zmod.unsigned (N.v26466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26466 s i)) at 1.
  unfold R.v26466, N.v26466.
  rewrite ?node_26464.
  rewrite ?node_26465.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26467 (s : N.State) (i : N.Inputs) :
  R.v26467 (state s) (inputs i) = Zmod.unsigned (N.v26467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26467 s i)) at 1.
  unfold R.v26467, N.v26467.
  rewrite ?node_26463.
  rewrite ?node_26466.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26468 (s : N.State) (i : N.Inputs) :
  R.v26468 (state s) (inputs i) = Zmod.unsigned (N.v26468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26468 s i)) at 1.
  unfold R.v26468, N.v26468.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26469 (s : N.State) (i : N.Inputs) :
  R.v26469 (state s) (inputs i) = Zmod.unsigned (N.v26469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26469 s i)) at 1.
  unfold R.v26469, N.v26469.
  rewrite ?node_10129.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26470 (s : N.State) (i : N.Inputs) :
  R.v26470 (state s) (inputs i) = Zmod.unsigned (N.v26470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26470 s i)) at 1.
  unfold R.v26470, N.v26470.
  unfold R.v6, N.v6.
  rewrite !state_r1090_nr_5F1090.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1090_nr_5F1090 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26471 (s : N.State) (i : N.Inputs) :
  R.v26471 (state s) (inputs i) = Zmod.unsigned (N.v26471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26471 s i)) at 1.
  unfold R.v26471, N.v26471.
  unfold R.v6, N.v6.
  rewrite ?node_10125.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26472 (s : N.State) (i : N.Inputs) :
  R.v26472 (state s) (inputs i) = Zmod.unsigned (N.v26472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26472 s i)) at 1.
  unfold R.v26472, N.v26472.
  rewrite ?node_26470.
  rewrite ?node_26471.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26473 (s : N.State) (i : N.Inputs) :
  R.v26473 (state s) (inputs i) = Zmod.unsigned (N.v26473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26473 s i)) at 1.
  unfold R.v26473, N.v26473.
  unfold R.v16484, N.v16484.
  rewrite ?node_26472.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26474 (s : N.State) (i : N.Inputs) :
  R.v26474 (state s) (inputs i) = Zmod.unsigned (N.v26474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26474 s i)) at 1.
  unfold R.v26474, N.v26474.
  rewrite ?node_26469.
  rewrite ?node_26473.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26475 (s : N.State) (i : N.Inputs) :
  R.v26475 (state s) (inputs i) = Zmod.unsigned (N.v26475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26475 s i)) at 1.
  unfold R.v26475, N.v26475.
  unfold R.v6, N.v6.
  rewrite ?node_26474.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26476 (s : N.State) (i : N.Inputs) :
  R.v26476 (state s) (inputs i) = Zmod.unsigned (N.v26476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26476 s i)) at 1.
  unfold R.v26476, N.v26476.
  rewrite ?node_10130.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26477 (s : N.State) (i : N.Inputs) :
  R.v26477 (state s) (inputs i) = Zmod.unsigned (N.v26477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26477 s i)) at 1.
  unfold R.v26477, N.v26477.
  unfold R.v6, N.v6.
  rewrite ?node_10355.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26478 (s : N.State) (i : N.Inputs) :
  R.v26478 (state s) (inputs i) = Zmod.unsigned (N.v26478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26478 s i)) at 1.
  unfold R.v26478, N.v26478.
  rewrite ?node_26476.
  rewrite ?node_26477.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26479 (s : N.State) (i : N.Inputs) :
  R.v26479 (state s) (inputs i) = Zmod.unsigned (N.v26479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26479 s i)) at 1.
  unfold R.v26479, N.v26479.
  rewrite ?node_26475.
  rewrite ?node_26478.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26480 (s : N.State) (i : N.Inputs) :
  R.v26480 (state s) (inputs i) = Zmod.unsigned (N.v26480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26480 s i)) at 1.
  unfold R.v26480, N.v26480.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26481 (s : N.State) (i : N.Inputs) :
  R.v26481 (state s) (inputs i) = Zmod.unsigned (N.v26481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26481 s i)) at 1.
  unfold R.v26481, N.v26481.
  rewrite ?node_10136.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26482 (s : N.State) (i : N.Inputs) :
  R.v26482 (state s) (inputs i) = Zmod.unsigned (N.v26482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26482 s i)) at 1.
  unfold R.v26482, N.v26482.
  unfold R.v16463, N.v16463.
  rewrite !state_r1094_nr_5F1094.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1094_nr_5F1094 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26483 (s : N.State) (i : N.Inputs) :
  R.v26483 (state s) (inputs i) = Zmod.unsigned (N.v26483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26483 s i)) at 1.
  unfold R.v26483, N.v26483.
  unfold R.v16463, N.v16463.
  rewrite !state_r1093_nr_5F1093.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1093_nr_5F1093 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26484 (s : N.State) (i : N.Inputs) :
  R.v26484 (state s) (inputs i) = Zmod.unsigned (N.v26484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26484 s i)) at 1.
  unfold R.v26484, N.v26484.
  unfold R.v6, N.v6.
  rewrite !state_r1092_nr_5F1092.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1092_nr_5F1092 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26485 (s : N.State) (i : N.Inputs) :
  R.v26485 (state s) (inputs i) = Zmod.unsigned (N.v26485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26485 s i)) at 1.
  unfold R.v26485, N.v26485.
  unfold R.v6, N.v6.
  rewrite !state_r1091_nr_5F1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1091_nr_5F1091 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26486 (s : N.State) (i : N.Inputs) :
  R.v26486 (state s) (inputs i) = Zmod.unsigned (N.v26486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26486 s i)) at 1.
  unfold R.v26486, N.v26486.
  rewrite ?node_26484.
  rewrite ?node_26485.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26487 (s : N.State) (i : N.Inputs) :
  R.v26487 (state s) (inputs i) = Zmod.unsigned (N.v26487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26487 s i)) at 1.
  unfold R.v26487, N.v26487.
  unfold R.v16484, N.v16484.
  rewrite ?node_26486.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26488 (s : N.State) (i : N.Inputs) :
  R.v26488 (state s) (inputs i) = Zmod.unsigned (N.v26488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26488 s i)) at 1.
  unfold R.v26488, N.v26488.
  rewrite ?node_26481.
  rewrite ?node_26482.
  rewrite ?node_26483.
  rewrite ?node_26487.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26489 (s : N.State) (i : N.Inputs) :
  R.v26489 (state s) (inputs i) = Zmod.unsigned (N.v26489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26489 s i)) at 1.
  unfold R.v26489, N.v26489.
  unfold R.v6, N.v6.
  rewrite ?node_26488.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26490 (s : N.State) (i : N.Inputs) :
  R.v26490 (state s) (inputs i) = Zmod.unsigned (N.v26490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26490 s i)) at 1.
  unfold R.v26490, N.v26490.
  rewrite ?node_10137.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26491 (s : N.State) (i : N.Inputs) :
  R.v26491 (state s) (inputs i) = Zmod.unsigned (N.v26491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26491 s i)) at 1.
  unfold R.v26491, N.v26491.
  unfold R.v6, N.v6.
  rewrite ?node_10293.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26492 (s : N.State) (i : N.Inputs) :
  R.v26492 (state s) (inputs i) = Zmod.unsigned (N.v26492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26492 s i)) at 1.
  unfold R.v26492, N.v26492.
  unfold R.v6, N.v6.
  rewrite ?node_10359.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26493 (s : N.State) (i : N.Inputs) :
  R.v26493 (state s) (inputs i) = Zmod.unsigned (N.v26493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26493 s i)) at 1.
  unfold R.v26493, N.v26493.
  rewrite ?node_26490.
  rewrite ?node_26491.
  rewrite ?node_26492.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26494 (s : N.State) (i : N.Inputs) :
  R.v26494 (state s) (inputs i) = Zmod.unsigned (N.v26494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26494 s i)) at 1.
  unfold R.v26494, N.v26494.
  rewrite ?node_26489.
  rewrite ?node_26493.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26495 (s : N.State) (i : N.Inputs) :
  R.v26495 (state s) (inputs i) = Zmod.unsigned (N.v26495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26495 s i)) at 1.
  unfold R.v26495, N.v26495.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26496 (s : N.State) (i : N.Inputs) :
  R.v26496 (state s) (inputs i) = Zmod.unsigned (N.v26496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26496 s i)) at 1.
  unfold R.v26496, N.v26496.
  unfold R.v16463, N.v16463.
  rewrite !state_r1093_nr_5F1093.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1093_nr_5F1093 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26497 (s : N.State) (i : N.Inputs) :
  R.v26497 (state s) (inputs i) = Zmod.unsigned (N.v26497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26497 s i)) at 1.
  unfold R.v26497, N.v26497.
  unfold R.v6, N.v6.
  rewrite !state_r1092_nr_5F1092.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1092_nr_5F1092 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26498 (s : N.State) (i : N.Inputs) :
  R.v26498 (state s) (inputs i) = Zmod.unsigned (N.v26498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26498 s i)) at 1.
  unfold R.v26498, N.v26498.
  unfold R.v6, N.v6.
  rewrite !state_r1091_nr_5F1091.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1091_nr_5F1091 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26499 (s : N.State) (i : N.Inputs) :
  R.v26499 (state s) (inputs i) = Zmod.unsigned (N.v26499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26499 s i)) at 1.
  unfold R.v26499, N.v26499.
  rewrite ?node_26497.
  rewrite ?node_26498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26500 (s : N.State) (i : N.Inputs) :
  R.v26500 (state s) (inputs i) = Zmod.unsigned (N.v26500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26500 s i)) at 1.
  unfold R.v26500, N.v26500.
  unfold R.v16484, N.v16484.
  rewrite ?node_26499.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26501 (s : N.State) (i : N.Inputs) :
  R.v26501 (state s) (inputs i) = Zmod.unsigned (N.v26501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26501 s i)) at 1.
  unfold R.v26501, N.v26501.
  rewrite ?node_26496.
  rewrite ?node_26500.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26502 (s : N.State) (i : N.Inputs) :
  R.v26502 (state s) (inputs i) = Zmod.unsigned (N.v26502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26502 s i)) at 1.
  unfold R.v26502, N.v26502.
  unfold R.v6, N.v6.
  rewrite ?node_26501.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26503 (s : N.State) (i : N.Inputs) :
  R.v26503 (state s) (inputs i) = Zmod.unsigned (N.v26503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26503 s i)) at 1.
  unfold R.v26503, N.v26503.
  rewrite ?node_10132.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26504 (s : N.State) (i : N.Inputs) :
  R.v26504 (state s) (inputs i) = Zmod.unsigned (N.v26504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26504 s i)) at 1.
  unfold R.v26504, N.v26504.
  unfold R.v6, N.v6.
  rewrite ?node_10293.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26505 (s : N.State) (i : N.Inputs) :
  R.v26505 (state s) (inputs i) = Zmod.unsigned (N.v26505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26505 s i)) at 1.
  unfold R.v26505, N.v26505.
  rewrite ?node_26503.
  rewrite ?node_26504.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26506 (s : N.State) (i : N.Inputs) :
  R.v26506 (state s) (inputs i) = Zmod.unsigned (N.v26506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26506 s i)) at 1.
  unfold R.v26506, N.v26506.
  rewrite ?node_26502.
  rewrite ?node_26505.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26507 (s : N.State) (i : N.Inputs) :
  R.v26507 (state s) (inputs i) = Zmod.unsigned (N.v26507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26507 s i)) at 1.
  unfold R.v26507, N.v26507.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26508 (s : N.State) (i : N.Inputs) :
  R.v26508 (state s) (inputs i) = Zmod.unsigned (N.v26508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26508 s i)) at 1.
  unfold R.v26508, N.v26508.
  rewrite ?node_10136.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26509 (s : N.State) (i : N.Inputs) :
  R.v26509 (state s) (inputs i) = Zmod.unsigned (N.v26509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26509 s i)) at 1.
  unfold R.v26509, N.v26509.
  unfold R.v6, N.v6.
  rewrite !state_r1094_nr_5F1094.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1094_nr_5F1094 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26510 (s : N.State) (i : N.Inputs) :
  R.v26510 (state s) (inputs i) = Zmod.unsigned (N.v26510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26510 s i)) at 1.
  unfold R.v26510, N.v26510.
  unfold R.v6, N.v6.
  rewrite ?node_10132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26511 (s : N.State) (i : N.Inputs) :
  R.v26511 (state s) (inputs i) = Zmod.unsigned (N.v26511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26511 s i)) at 1.
  unfold R.v26511, N.v26511.
  rewrite ?node_26509.
  rewrite ?node_26510.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26512 (s : N.State) (i : N.Inputs) :
  R.v26512 (state s) (inputs i) = Zmod.unsigned (N.v26512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26512 s i)) at 1.
  unfold R.v26512, N.v26512.
  unfold R.v16484, N.v16484.
  rewrite ?node_26511.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26513 (s : N.State) (i : N.Inputs) :
  R.v26513 (state s) (inputs i) = Zmod.unsigned (N.v26513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26513 s i)) at 1.
  unfold R.v26513, N.v26513.
  rewrite ?node_26508.
  rewrite ?node_26512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26514 (s : N.State) (i : N.Inputs) :
  R.v26514 (state s) (inputs i) = Zmod.unsigned (N.v26514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26514 s i)) at 1.
  unfold R.v26514, N.v26514.
  unfold R.v6, N.v6.
  rewrite ?node_26513.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26515 (s : N.State) (i : N.Inputs) :
  R.v26515 (state s) (inputs i) = Zmod.unsigned (N.v26515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26515 s i)) at 1.
  unfold R.v26515, N.v26515.
  rewrite ?node_10137.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26516 (s : N.State) (i : N.Inputs) :
  R.v26516 (state s) (inputs i) = Zmod.unsigned (N.v26516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26516 s i)) at 1.
  unfold R.v26516, N.v26516.
  unfold R.v6, N.v6.
  rewrite ?node_10359.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26517 (s : N.State) (i : N.Inputs) :
  R.v26517 (state s) (inputs i) = Zmod.unsigned (N.v26517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26517 s i)) at 1.
  unfold R.v26517, N.v26517.
  rewrite ?node_26515.
  rewrite ?node_26516.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26518 (s : N.State) (i : N.Inputs) :
  R.v26518 (state s) (inputs i) = Zmod.unsigned (N.v26518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26518 s i)) at 1.
  unfold R.v26518, N.v26518.
  rewrite ?node_26514.
  rewrite ?node_26517.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26519 (s : N.State) (i : N.Inputs) :
  R.v26519 (state s) (inputs i) = Zmod.unsigned (N.v26519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26519 s i)) at 1.
  unfold R.v26519, N.v26519.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26520 (s : N.State) (i : N.Inputs) :
  R.v26520 (state s) (inputs i) = Zmod.unsigned (N.v26520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26520 s i)) at 1.
  unfold R.v26520, N.v26520.
  rewrite ?node_10144.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26521 (s : N.State) (i : N.Inputs) :
  R.v26521 (state s) (inputs i) = Zmod.unsigned (N.v26521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26521 s i)) at 1.
  unfold R.v26521, N.v26521.
  unfold R.v16463, N.v16463.
  rewrite !state_r1098_nr_5F1098.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1098_nr_5F1098 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26522 (s : N.State) (i : N.Inputs) :
  R.v26522 (state s) (inputs i) = Zmod.unsigned (N.v26522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26522 s i)) at 1.
  unfold R.v26522, N.v26522.
  unfold R.v16463, N.v16463.
  rewrite !state_r1097_nr_5F1097.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1097_nr_5F1097 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26523 (s : N.State) (i : N.Inputs) :
  R.v26523 (state s) (inputs i) = Zmod.unsigned (N.v26523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26523 s i)) at 1.
  unfold R.v26523, N.v26523.
  unfold R.v6, N.v6.
  rewrite !state_r1096_nr_5F1096.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1096_nr_5F1096 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26524 (s : N.State) (i : N.Inputs) :
  R.v26524 (state s) (inputs i) = Zmod.unsigned (N.v26524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26524 s i)) at 1.
  unfold R.v26524, N.v26524.
  unfold R.v6, N.v6.
  rewrite !state_r1095_nr_5F1095.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1095_nr_5F1095 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26525 (s : N.State) (i : N.Inputs) :
  R.v26525 (state s) (inputs i) = Zmod.unsigned (N.v26525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26525 s i)) at 1.
  unfold R.v26525, N.v26525.
  rewrite ?node_26523.
  rewrite ?node_26524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26526 (s : N.State) (i : N.Inputs) :
  R.v26526 (state s) (inputs i) = Zmod.unsigned (N.v26526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26526 s i)) at 1.
  unfold R.v26526, N.v26526.
  unfold R.v16484, N.v16484.
  rewrite ?node_26525.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26527 (s : N.State) (i : N.Inputs) :
  R.v26527 (state s) (inputs i) = Zmod.unsigned (N.v26527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26527 s i)) at 1.
  unfold R.v26527, N.v26527.
  rewrite ?node_26520.
  rewrite ?node_26521.
  rewrite ?node_26522.
  rewrite ?node_26526.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26528 (s : N.State) (i : N.Inputs) :
  R.v26528 (state s) (inputs i) = Zmod.unsigned (N.v26528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26528 s i)) at 1.
  unfold R.v26528, N.v26528.
  unfold R.v6, N.v6.
  rewrite ?node_26527.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26529 (s : N.State) (i : N.Inputs) :
  R.v26529 (state s) (inputs i) = Zmod.unsigned (N.v26529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26529 s i)) at 1.
  unfold R.v26529, N.v26529.
  rewrite ?node_10145.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26530 (s : N.State) (i : N.Inputs) :
  R.v26530 (state s) (inputs i) = Zmod.unsigned (N.v26530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26530 s i)) at 1.
  unfold R.v26530, N.v26530.
  unfold R.v6, N.v6.
  rewrite ?node_10301.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26531 (s : N.State) (i : N.Inputs) :
  R.v26531 (state s) (inputs i) = Zmod.unsigned (N.v26531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26531 s i)) at 1.
  unfold R.v26531, N.v26531.
  unfold R.v6, N.v6.
  rewrite ?node_10363.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26532 (s : N.State) (i : N.Inputs) :
  R.v26532 (state s) (inputs i) = Zmod.unsigned (N.v26532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26532 s i)) at 1.
  unfold R.v26532, N.v26532.
  rewrite ?node_26529.
  rewrite ?node_26530.
  rewrite ?node_26531.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26533 (s : N.State) (i : N.Inputs) :
  R.v26533 (state s) (inputs i) = Zmod.unsigned (N.v26533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26533 s i)) at 1.
  unfold R.v26533, N.v26533.
  rewrite ?node_26528.
  rewrite ?node_26532.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26534 (s : N.State) (i : N.Inputs) :
  R.v26534 (state s) (inputs i) = Zmod.unsigned (N.v26534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26534 s i)) at 1.
  unfold R.v26534, N.v26534.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26535 (s : N.State) (i : N.Inputs) :
  R.v26535 (state s) (inputs i) = Zmod.unsigned (N.v26535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26535 s i)) at 1.
  unfold R.v26535, N.v26535.
  unfold R.v16463, N.v16463.
  rewrite !state_r1097_nr_5F1097.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1097_nr_5F1097 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26536 (s : N.State) (i : N.Inputs) :
  R.v26536 (state s) (inputs i) = Zmod.unsigned (N.v26536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26536 s i)) at 1.
  unfold R.v26536, N.v26536.
  unfold R.v6, N.v6.
  rewrite !state_r1096_nr_5F1096.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1096_nr_5F1096 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26537 (s : N.State) (i : N.Inputs) :
  R.v26537 (state s) (inputs i) = Zmod.unsigned (N.v26537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26537 s i)) at 1.
  unfold R.v26537, N.v26537.
  unfold R.v6, N.v6.
  rewrite !state_r1095_nr_5F1095.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1095_nr_5F1095 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26538 (s : N.State) (i : N.Inputs) :
  R.v26538 (state s) (inputs i) = Zmod.unsigned (N.v26538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26538 s i)) at 1.
  unfold R.v26538, N.v26538.
  rewrite ?node_26536.
  rewrite ?node_26537.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26539 (s : N.State) (i : N.Inputs) :
  R.v26539 (state s) (inputs i) = Zmod.unsigned (N.v26539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26539 s i)) at 1.
  unfold R.v26539, N.v26539.
  unfold R.v16484, N.v16484.
  rewrite ?node_26538.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26540 (s : N.State) (i : N.Inputs) :
  R.v26540 (state s) (inputs i) = Zmod.unsigned (N.v26540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26540 s i)) at 1.
  unfold R.v26540, N.v26540.
  rewrite ?node_26535.
  rewrite ?node_26539.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26541 (s : N.State) (i : N.Inputs) :
  R.v26541 (state s) (inputs i) = Zmod.unsigned (N.v26541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26541 s i)) at 1.
  unfold R.v26541, N.v26541.
  unfold R.v6, N.v6.
  rewrite ?node_26540.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26542 (s : N.State) (i : N.Inputs) :
  R.v26542 (state s) (inputs i) = Zmod.unsigned (N.v26542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26542 s i)) at 1.
  unfold R.v26542, N.v26542.
  rewrite ?node_10140.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26543 (s : N.State) (i : N.Inputs) :
  R.v26543 (state s) (inputs i) = Zmod.unsigned (N.v26543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26543 s i)) at 1.
  unfold R.v26543, N.v26543.
  unfold R.v6, N.v6.
  rewrite ?node_10301.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26544 (s : N.State) (i : N.Inputs) :
  R.v26544 (state s) (inputs i) = Zmod.unsigned (N.v26544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26544 s i)) at 1.
  unfold R.v26544, N.v26544.
  rewrite ?node_26542.
  rewrite ?node_26543.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26545 (s : N.State) (i : N.Inputs) :
  R.v26545 (state s) (inputs i) = Zmod.unsigned (N.v26545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26545 s i)) at 1.
  unfold R.v26545, N.v26545.
  rewrite ?node_26541.
  rewrite ?node_26544.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26546 (s : N.State) (i : N.Inputs) :
  R.v26546 (state s) (inputs i) = Zmod.unsigned (N.v26546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26546 s i)) at 1.
  unfold R.v26546, N.v26546.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26547 (s : N.State) (i : N.Inputs) :
  R.v26547 (state s) (inputs i) = Zmod.unsigned (N.v26547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26547 s i)) at 1.
  unfold R.v26547, N.v26547.
  rewrite ?node_10144.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26548 (s : N.State) (i : N.Inputs) :
  R.v26548 (state s) (inputs i) = Zmod.unsigned (N.v26548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26548 s i)) at 1.
  unfold R.v26548, N.v26548.
  unfold R.v6, N.v6.
  rewrite !state_r1098_nr_5F1098.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1098_nr_5F1098 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26549 (s : N.State) (i : N.Inputs) :
  R.v26549 (state s) (inputs i) = Zmod.unsigned (N.v26549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26549 s i)) at 1.
  unfold R.v26549, N.v26549.
  unfold R.v6, N.v6.
  rewrite ?node_10140.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26550 (s : N.State) (i : N.Inputs) :
  R.v26550 (state s) (inputs i) = Zmod.unsigned (N.v26550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26550 s i)) at 1.
  unfold R.v26550, N.v26550.
  rewrite ?node_26548.
  rewrite ?node_26549.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26551 (s : N.State) (i : N.Inputs) :
  R.v26551 (state s) (inputs i) = Zmod.unsigned (N.v26551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26551 s i)) at 1.
  unfold R.v26551, N.v26551.
  unfold R.v16484, N.v16484.
  rewrite ?node_26550.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26552 (s : N.State) (i : N.Inputs) :
  R.v26552 (state s) (inputs i) = Zmod.unsigned (N.v26552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26552 s i)) at 1.
  unfold R.v26552, N.v26552.
  rewrite ?node_26547.
  rewrite ?node_26551.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26553 (s : N.State) (i : N.Inputs) :
  R.v26553 (state s) (inputs i) = Zmod.unsigned (N.v26553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26553 s i)) at 1.
  unfold R.v26553, N.v26553.
  unfold R.v6, N.v6.
  rewrite ?node_26552.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26554 (s : N.State) (i : N.Inputs) :
  R.v26554 (state s) (inputs i) = Zmod.unsigned (N.v26554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26554 s i)) at 1.
  unfold R.v26554, N.v26554.
  rewrite ?node_10145.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26555 (s : N.State) (i : N.Inputs) :
  R.v26555 (state s) (inputs i) = Zmod.unsigned (N.v26555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26555 s i)) at 1.
  unfold R.v26555, N.v26555.
  unfold R.v6, N.v6.
  rewrite ?node_10363.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26556 (s : N.State) (i : N.Inputs) :
  R.v26556 (state s) (inputs i) = Zmod.unsigned (N.v26556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26556 s i)) at 1.
  unfold R.v26556, N.v26556.
  rewrite ?node_26554.
  rewrite ?node_26555.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26557 (s : N.State) (i : N.Inputs) :
  R.v26557 (state s) (inputs i) = Zmod.unsigned (N.v26557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26557 s i)) at 1.
  unfold R.v26557, N.v26557.
  rewrite ?node_26553.
  rewrite ?node_26556.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26558 (s : N.State) (i : N.Inputs) :
  R.v26558 (state s) (inputs i) = Zmod.unsigned (N.v26558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26558 s i)) at 1.
  unfold R.v26558, N.v26558.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26559 (s : N.State) (i : N.Inputs) :
  R.v26559 (state s) (inputs i) = Zmod.unsigned (N.v26559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26559 s i)) at 1.
  unfold R.v26559, N.v26559.
  rewrite ?node_10152.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26560 (s : N.State) (i : N.Inputs) :
  R.v26560 (state s) (inputs i) = Zmod.unsigned (N.v26560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26560 s i)) at 1.
  unfold R.v26560, N.v26560.
  unfold R.v16463, N.v16463.
  rewrite !state_r1102_nr_5F1102.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1102_nr_5F1102 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26561 (s : N.State) (i : N.Inputs) :
  R.v26561 (state s) (inputs i) = Zmod.unsigned (N.v26561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26561 s i)) at 1.
  unfold R.v26561, N.v26561.
  unfold R.v16463, N.v16463.
  rewrite !state_r1101_nr_5F1101.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1101_nr_5F1101 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26562 (s : N.State) (i : N.Inputs) :
  R.v26562 (state s) (inputs i) = Zmod.unsigned (N.v26562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26562 s i)) at 1.
  unfold R.v26562, N.v26562.
  unfold R.v6, N.v6.
  rewrite !state_r1100_nr_5F1100.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1100_nr_5F1100 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26563 (s : N.State) (i : N.Inputs) :
  R.v26563 (state s) (inputs i) = Zmod.unsigned (N.v26563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26563 s i)) at 1.
  unfold R.v26563, N.v26563.
  unfold R.v6, N.v6.
  rewrite !state_r1099_nr_5F1099.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1099_nr_5F1099 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26564 (s : N.State) (i : N.Inputs) :
  R.v26564 (state s) (inputs i) = Zmod.unsigned (N.v26564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26564 s i)) at 1.
  unfold R.v26564, N.v26564.
  rewrite ?node_26562.
  rewrite ?node_26563.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26565 (s : N.State) (i : N.Inputs) :
  R.v26565 (state s) (inputs i) = Zmod.unsigned (N.v26565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26565 s i)) at 1.
  unfold R.v26565, N.v26565.
  unfold R.v16484, N.v16484.
  rewrite ?node_26564.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26566 (s : N.State) (i : N.Inputs) :
  R.v26566 (state s) (inputs i) = Zmod.unsigned (N.v26566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26566 s i)) at 1.
  unfold R.v26566, N.v26566.
  rewrite ?node_26559.
  rewrite ?node_26560.
  rewrite ?node_26561.
  rewrite ?node_26565.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26567 (s : N.State) (i : N.Inputs) :
  R.v26567 (state s) (inputs i) = Zmod.unsigned (N.v26567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26567 s i)) at 1.
  unfold R.v26567, N.v26567.
  unfold R.v6, N.v6.
  rewrite ?node_26566.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26568 (s : N.State) (i : N.Inputs) :
  R.v26568 (state s) (inputs i) = Zmod.unsigned (N.v26568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26568 s i)) at 1.
  unfold R.v26568, N.v26568.
  rewrite ?node_10153.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26569 (s : N.State) (i : N.Inputs) :
  R.v26569 (state s) (inputs i) = Zmod.unsigned (N.v26569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26569 s i)) at 1.
  unfold R.v26569, N.v26569.
  unfold R.v6, N.v6.
  rewrite ?node_10309.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26570 (s : N.State) (i : N.Inputs) :
  R.v26570 (state s) (inputs i) = Zmod.unsigned (N.v26570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26570 s i)) at 1.
  unfold R.v26570, N.v26570.
  unfold R.v6, N.v6.
  rewrite ?node_10372.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26571 (s : N.State) (i : N.Inputs) :
  R.v26571 (state s) (inputs i) = Zmod.unsigned (N.v26571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26571 s i)) at 1.
  unfold R.v26571, N.v26571.
  rewrite ?node_26568.
  rewrite ?node_26569.
  rewrite ?node_26570.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26572 (s : N.State) (i : N.Inputs) :
  R.v26572 (state s) (inputs i) = Zmod.unsigned (N.v26572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26572 s i)) at 1.
  unfold R.v26572, N.v26572.
  rewrite ?node_26567.
  rewrite ?node_26571.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26573 (s : N.State) (i : N.Inputs) :
  R.v26573 (state s) (inputs i) = Zmod.unsigned (N.v26573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26573 s i)) at 1.
  unfold R.v26573, N.v26573.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26574 (s : N.State) (i : N.Inputs) :
  R.v26574 (state s) (inputs i) = Zmod.unsigned (N.v26574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26574 s i)) at 1.
  unfold R.v26574, N.v26574.
  unfold R.v16463, N.v16463.
  rewrite !state_r1101_nr_5F1101.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1101_nr_5F1101 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26575 (s : N.State) (i : N.Inputs) :
  R.v26575 (state s) (inputs i) = Zmod.unsigned (N.v26575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26575 s i)) at 1.
  unfold R.v26575, N.v26575.
  unfold R.v6, N.v6.
  rewrite !state_r1100_nr_5F1100.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1100_nr_5F1100 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26576 (s : N.State) (i : N.Inputs) :
  R.v26576 (state s) (inputs i) = Zmod.unsigned (N.v26576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26576 s i)) at 1.
  unfold R.v26576, N.v26576.
  unfold R.v6, N.v6.
  rewrite !state_r1099_nr_5F1099.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1099_nr_5F1099 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26577 (s : N.State) (i : N.Inputs) :
  R.v26577 (state s) (inputs i) = Zmod.unsigned (N.v26577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26577 s i)) at 1.
  unfold R.v26577, N.v26577.
  rewrite ?node_26575.
  rewrite ?node_26576.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26578 (s : N.State) (i : N.Inputs) :
  R.v26578 (state s) (inputs i) = Zmod.unsigned (N.v26578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26578 s i)) at 1.
  unfold R.v26578, N.v26578.
  unfold R.v16484, N.v16484.
  rewrite ?node_26577.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26579 (s : N.State) (i : N.Inputs) :
  R.v26579 (state s) (inputs i) = Zmod.unsigned (N.v26579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26579 s i)) at 1.
  unfold R.v26579, N.v26579.
  rewrite ?node_26574.
  rewrite ?node_26578.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26580 (s : N.State) (i : N.Inputs) :
  R.v26580 (state s) (inputs i) = Zmod.unsigned (N.v26580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26580 s i)) at 1.
  unfold R.v26580, N.v26580.
  unfold R.v6, N.v6.
  rewrite ?node_26579.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26581 (s : N.State) (i : N.Inputs) :
  R.v26581 (state s) (inputs i) = Zmod.unsigned (N.v26581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26581 s i)) at 1.
  unfold R.v26581, N.v26581.
  rewrite ?node_10148.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26582 (s : N.State) (i : N.Inputs) :
  R.v26582 (state s) (inputs i) = Zmod.unsigned (N.v26582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26582 s i)) at 1.
  unfold R.v26582, N.v26582.
  unfold R.v6, N.v6.
  rewrite ?node_10309.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26583 (s : N.State) (i : N.Inputs) :
  R.v26583 (state s) (inputs i) = Zmod.unsigned (N.v26583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26583 s i)) at 1.
  unfold R.v26583, N.v26583.
  rewrite ?node_26581.
  rewrite ?node_26582.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26584 (s : N.State) (i : N.Inputs) :
  R.v26584 (state s) (inputs i) = Zmod.unsigned (N.v26584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26584 s i)) at 1.
  unfold R.v26584, N.v26584.
  rewrite ?node_26580.
  rewrite ?node_26583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26585 (s : N.State) (i : N.Inputs) :
  R.v26585 (state s) (inputs i) = Zmod.unsigned (N.v26585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26585 s i)) at 1.
  unfold R.v26585, N.v26585.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26586 (s : N.State) (i : N.Inputs) :
  R.v26586 (state s) (inputs i) = Zmod.unsigned (N.v26586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26586 s i)) at 1.
  unfold R.v26586, N.v26586.
  rewrite ?node_10152.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26587 (s : N.State) (i : N.Inputs) :
  R.v26587 (state s) (inputs i) = Zmod.unsigned (N.v26587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26587 s i)) at 1.
  unfold R.v26587, N.v26587.
  unfold R.v6, N.v6.
  rewrite !state_r1102_nr_5F1102.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1102_nr_5F1102 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26588 (s : N.State) (i : N.Inputs) :
  R.v26588 (state s) (inputs i) = Zmod.unsigned (N.v26588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26588 s i)) at 1.
  unfold R.v26588, N.v26588.
  unfold R.v6, N.v6.
  rewrite ?node_10148.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26589 (s : N.State) (i : N.Inputs) :
  R.v26589 (state s) (inputs i) = Zmod.unsigned (N.v26589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26589 s i)) at 1.
  unfold R.v26589, N.v26589.
  rewrite ?node_26587.
  rewrite ?node_26588.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26590 (s : N.State) (i : N.Inputs) :
  R.v26590 (state s) (inputs i) = Zmod.unsigned (N.v26590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26590 s i)) at 1.
  unfold R.v26590, N.v26590.
  unfold R.v16484, N.v16484.
  rewrite ?node_26589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26591 (s : N.State) (i : N.Inputs) :
  R.v26591 (state s) (inputs i) = Zmod.unsigned (N.v26591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26591 s i)) at 1.
  unfold R.v26591, N.v26591.
  rewrite ?node_26586.
  rewrite ?node_26590.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26592 (s : N.State) (i : N.Inputs) :
  R.v26592 (state s) (inputs i) = Zmod.unsigned (N.v26592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26592 s i)) at 1.
  unfold R.v26592, N.v26592.
  unfold R.v6, N.v6.
  rewrite ?node_26591.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26593 (s : N.State) (i : N.Inputs) :
  R.v26593 (state s) (inputs i) = Zmod.unsigned (N.v26593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26593 s i)) at 1.
  unfold R.v26593, N.v26593.
  rewrite ?node_10153.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26594 (s : N.State) (i : N.Inputs) :
  R.v26594 (state s) (inputs i) = Zmod.unsigned (N.v26594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26594 s i)) at 1.
  unfold R.v26594, N.v26594.
  unfold R.v6, N.v6.
  rewrite ?node_10372.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26595 (s : N.State) (i : N.Inputs) :
  R.v26595 (state s) (inputs i) = Zmod.unsigned (N.v26595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26595 s i)) at 1.
  unfold R.v26595, N.v26595.
  rewrite ?node_26593.
  rewrite ?node_26594.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26596 (s : N.State) (i : N.Inputs) :
  R.v26596 (state s) (inputs i) = Zmod.unsigned (N.v26596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26596 s i)) at 1.
  unfold R.v26596, N.v26596.
  rewrite ?node_26592.
  rewrite ?node_26595.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26597 (s : N.State) (i : N.Inputs) :
  R.v26597 (state s) (inputs i) = Zmod.unsigned (N.v26597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26597 s i)) at 1.
  unfold R.v26597, N.v26597.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26598 (s : N.State) (i : N.Inputs) :
  R.v26598 (state s) (inputs i) = Zmod.unsigned (N.v26598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26598 s i)) at 1.
  unfold R.v26598, N.v26598.
  rewrite ?node_10164.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26599 (s : N.State) (i : N.Inputs) :
  R.v26599 (state s) (inputs i) = Zmod.unsigned (N.v26599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26599 s i)) at 1.
  unfold R.v26599, N.v26599.
  unfold R.v16463, N.v16463.
  rewrite !state_r1106_nr_5F1106.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1106_nr_5F1106 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26600 (s : N.State) (i : N.Inputs) :
  R.v26600 (state s) (inputs i) = Zmod.unsigned (N.v26600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26600 s i)) at 1.
  unfold R.v26600, N.v26600.
  unfold R.v16463, N.v16463.
  rewrite !state_r1105_nr_5F1105.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1105_nr_5F1105 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26601 (s : N.State) (i : N.Inputs) :
  R.v26601 (state s) (inputs i) = Zmod.unsigned (N.v26601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26601 s i)) at 1.
  unfold R.v26601, N.v26601.
  unfold R.v6, N.v6.
  rewrite !state_r1104_nr_5F1104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1104_nr_5F1104 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26602 (s : N.State) (i : N.Inputs) :
  R.v26602 (state s) (inputs i) = Zmod.unsigned (N.v26602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26602 s i)) at 1.
  unfold R.v26602, N.v26602.
  unfold R.v6, N.v6.
  rewrite !state_r1103_nr_5F1103.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1103_nr_5F1103 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26603 (s : N.State) (i : N.Inputs) :
  R.v26603 (state s) (inputs i) = Zmod.unsigned (N.v26603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26603 s i)) at 1.
  unfold R.v26603, N.v26603.
  rewrite ?node_26601.
  rewrite ?node_26602.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26604 (s : N.State) (i : N.Inputs) :
  R.v26604 (state s) (inputs i) = Zmod.unsigned (N.v26604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26604 s i)) at 1.
  unfold R.v26604, N.v26604.
  unfold R.v16484, N.v16484.
  rewrite ?node_26603.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26605 (s : N.State) (i : N.Inputs) :
  R.v26605 (state s) (inputs i) = Zmod.unsigned (N.v26605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26605 s i)) at 1.
  unfold R.v26605, N.v26605.
  rewrite ?node_26598.
  rewrite ?node_26599.
  rewrite ?node_26600.
  rewrite ?node_26604.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26606 (s : N.State) (i : N.Inputs) :
  R.v26606 (state s) (inputs i) = Zmod.unsigned (N.v26606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26606 s i)) at 1.
  unfold R.v26606, N.v26606.
  unfold R.v6, N.v6.
  rewrite ?node_26605.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26607 (s : N.State) (i : N.Inputs) :
  R.v26607 (state s) (inputs i) = Zmod.unsigned (N.v26607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26607 s i)) at 1.
  unfold R.v26607, N.v26607.
  rewrite ?node_10165.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26608 (s : N.State) (i : N.Inputs) :
  R.v26608 (state s) (inputs i) = Zmod.unsigned (N.v26608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26608 s i)) at 1.
  unfold R.v26608, N.v26608.
  unfold R.v6, N.v6.
  rewrite ?node_10321.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26609 (s : N.State) (i : N.Inputs) :
  R.v26609 (state s) (inputs i) = Zmod.unsigned (N.v26609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26609 s i)) at 1.
  unfold R.v26609, N.v26609.
  unfold R.v6, N.v6.
  rewrite ?node_10375.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26610 (s : N.State) (i : N.Inputs) :
  R.v26610 (state s) (inputs i) = Zmod.unsigned (N.v26610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26610 s i)) at 1.
  unfold R.v26610, N.v26610.
  rewrite ?node_26607.
  rewrite ?node_26608.
  rewrite ?node_26609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26611 (s : N.State) (i : N.Inputs) :
  R.v26611 (state s) (inputs i) = Zmod.unsigned (N.v26611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26611 s i)) at 1.
  unfold R.v26611, N.v26611.
  rewrite ?node_26606.
  rewrite ?node_26610.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26612 (s : N.State) (i : N.Inputs) :
  R.v26612 (state s) (inputs i) = Zmod.unsigned (N.v26612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26612 s i)) at 1.
  unfold R.v26612, N.v26612.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26613 (s : N.State) (i : N.Inputs) :
  R.v26613 (state s) (inputs i) = Zmod.unsigned (N.v26613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26613 s i)) at 1.
  unfold R.v26613, N.v26613.
  unfold R.v16463, N.v16463.
  rewrite !state_r1105_nr_5F1105.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1105_nr_5F1105 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26614 (s : N.State) (i : N.Inputs) :
  R.v26614 (state s) (inputs i) = Zmod.unsigned (N.v26614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26614 s i)) at 1.
  unfold R.v26614, N.v26614.
  unfold R.v6, N.v6.
  rewrite !state_r1104_nr_5F1104.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1104_nr_5F1104 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26615 (s : N.State) (i : N.Inputs) :
  R.v26615 (state s) (inputs i) = Zmod.unsigned (N.v26615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26615 s i)) at 1.
  unfold R.v26615, N.v26615.
  unfold R.v6, N.v6.
  rewrite !state_r1103_nr_5F1103.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1103_nr_5F1103 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26616 (s : N.State) (i : N.Inputs) :
  R.v26616 (state s) (inputs i) = Zmod.unsigned (N.v26616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26616 s i)) at 1.
  unfold R.v26616, N.v26616.
  rewrite ?node_26614.
  rewrite ?node_26615.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26617 (s : N.State) (i : N.Inputs) :
  R.v26617 (state s) (inputs i) = Zmod.unsigned (N.v26617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26617 s i)) at 1.
  unfold R.v26617, N.v26617.
  unfold R.v16484, N.v16484.
  rewrite ?node_26616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26618 (s : N.State) (i : N.Inputs) :
  R.v26618 (state s) (inputs i) = Zmod.unsigned (N.v26618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26618 s i)) at 1.
  unfold R.v26618, N.v26618.
  rewrite ?node_26613.
  rewrite ?node_26617.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26619 (s : N.State) (i : N.Inputs) :
  R.v26619 (state s) (inputs i) = Zmod.unsigned (N.v26619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26619 s i)) at 1.
  unfold R.v26619, N.v26619.
  unfold R.v6, N.v6.
  rewrite ?node_26618.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26620 (s : N.State) (i : N.Inputs) :
  R.v26620 (state s) (inputs i) = Zmod.unsigned (N.v26620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26620 s i)) at 1.
  unfold R.v26620, N.v26620.
  rewrite ?node_10160.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26621 (s : N.State) (i : N.Inputs) :
  R.v26621 (state s) (inputs i) = Zmod.unsigned (N.v26621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26621 s i)) at 1.
  unfold R.v26621, N.v26621.
  unfold R.v6, N.v6.
  rewrite ?node_10321.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26622 (s : N.State) (i : N.Inputs) :
  R.v26622 (state s) (inputs i) = Zmod.unsigned (N.v26622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26622 s i)) at 1.
  unfold R.v26622, N.v26622.
  rewrite ?node_26620.
  rewrite ?node_26621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26623 (s : N.State) (i : N.Inputs) :
  R.v26623 (state s) (inputs i) = Zmod.unsigned (N.v26623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26623 s i)) at 1.
  unfold R.v26623, N.v26623.
  rewrite ?node_26619.
  rewrite ?node_26622.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26624 (s : N.State) (i : N.Inputs) :
  R.v26624 (state s) (inputs i) = Zmod.unsigned (N.v26624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26624 s i)) at 1.
  unfold R.v26624, N.v26624.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26625 (s : N.State) (i : N.Inputs) :
  R.v26625 (state s) (inputs i) = Zmod.unsigned (N.v26625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26625 s i)) at 1.
  unfold R.v26625, N.v26625.
  rewrite ?node_10164.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26626 (s : N.State) (i : N.Inputs) :
  R.v26626 (state s) (inputs i) = Zmod.unsigned (N.v26626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26626 s i)) at 1.
  unfold R.v26626, N.v26626.
  unfold R.v6, N.v6.
  rewrite !state_r1106_nr_5F1106.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1106_nr_5F1106 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26627 (s : N.State) (i : N.Inputs) :
  R.v26627 (state s) (inputs i) = Zmod.unsigned (N.v26627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26627 s i)) at 1.
  unfold R.v26627, N.v26627.
  unfold R.v6, N.v6.
  rewrite ?node_10160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26628 (s : N.State) (i : N.Inputs) :
  R.v26628 (state s) (inputs i) = Zmod.unsigned (N.v26628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26628 s i)) at 1.
  unfold R.v26628, N.v26628.
  rewrite ?node_26626.
  rewrite ?node_26627.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26629 (s : N.State) (i : N.Inputs) :
  R.v26629 (state s) (inputs i) = Zmod.unsigned (N.v26629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26629 s i)) at 1.
  unfold R.v26629, N.v26629.
  unfold R.v16484, N.v16484.
  rewrite ?node_26628.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26630 (s : N.State) (i : N.Inputs) :
  R.v26630 (state s) (inputs i) = Zmod.unsigned (N.v26630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26630 s i)) at 1.
  unfold R.v26630, N.v26630.
  rewrite ?node_26625.
  rewrite ?node_26629.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26631 (s : N.State) (i : N.Inputs) :
  R.v26631 (state s) (inputs i) = Zmod.unsigned (N.v26631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26631 s i)) at 1.
  unfold R.v26631, N.v26631.
  unfold R.v6, N.v6.
  rewrite ?node_26630.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26632 (s : N.State) (i : N.Inputs) :
  R.v26632 (state s) (inputs i) = Zmod.unsigned (N.v26632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26632 s i)) at 1.
  unfold R.v26632, N.v26632.
  rewrite ?node_10165.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26633 (s : N.State) (i : N.Inputs) :
  R.v26633 (state s) (inputs i) = Zmod.unsigned (N.v26633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26633 s i)) at 1.
  unfold R.v26633, N.v26633.
  unfold R.v6, N.v6.
  rewrite ?node_10375.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26634 (s : N.State) (i : N.Inputs) :
  R.v26634 (state s) (inputs i) = Zmod.unsigned (N.v26634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26634 s i)) at 1.
  unfold R.v26634, N.v26634.
  rewrite ?node_26632.
  rewrite ?node_26633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26635 (s : N.State) (i : N.Inputs) :
  R.v26635 (state s) (inputs i) = Zmod.unsigned (N.v26635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26635 s i)) at 1.
  unfold R.v26635, N.v26635.
  rewrite ?node_26631.
  rewrite ?node_26634.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26636 (s : N.State) (i : N.Inputs) :
  R.v26636 (state s) (inputs i) = Zmod.unsigned (N.v26636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26636 s i)) at 1.
  unfold R.v26636, N.v26636.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26637 (s : N.State) (i : N.Inputs) :
  R.v26637 (state s) (inputs i) = Zmod.unsigned (N.v26637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26637 s i)) at 1.
  unfold R.v26637, N.v26637.
  rewrite ?node_10171.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26638 (s : N.State) (i : N.Inputs) :
  R.v26638 (state s) (inputs i) = Zmod.unsigned (N.v26638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26638 s i)) at 1.
  unfold R.v26638, N.v26638.
  unfold R.v16463, N.v16463.
  rewrite !state_r1110_nr_5F1110.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1110_nr_5F1110 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26639 (s : N.State) (i : N.Inputs) :
  R.v26639 (state s) (inputs i) = Zmod.unsigned (N.v26639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26639 s i)) at 1.
  unfold R.v26639, N.v26639.
  unfold R.v16463, N.v16463.
  rewrite !state_r1109_nr_5F1109.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1109_nr_5F1109 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26640 (s : N.State) (i : N.Inputs) :
  R.v26640 (state s) (inputs i) = Zmod.unsigned (N.v26640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26640 s i)) at 1.
  unfold R.v26640, N.v26640.
  unfold R.v6, N.v6.
  rewrite !state_r1108_nr_5F1108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1108_nr_5F1108 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26641 (s : N.State) (i : N.Inputs) :
  R.v26641 (state s) (inputs i) = Zmod.unsigned (N.v26641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26641 s i)) at 1.
  unfold R.v26641, N.v26641.
  unfold R.v6, N.v6.
  rewrite !state_r1107_nr_5F1107.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1107_nr_5F1107 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26642 (s : N.State) (i : N.Inputs) :
  R.v26642 (state s) (inputs i) = Zmod.unsigned (N.v26642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26642 s i)) at 1.
  unfold R.v26642, N.v26642.
  rewrite ?node_26640.
  rewrite ?node_26641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26643 (s : N.State) (i : N.Inputs) :
  R.v26643 (state s) (inputs i) = Zmod.unsigned (N.v26643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26643 s i)) at 1.
  unfold R.v26643, N.v26643.
  unfold R.v16484, N.v16484.
  rewrite ?node_26642.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26644 (s : N.State) (i : N.Inputs) :
  R.v26644 (state s) (inputs i) = Zmod.unsigned (N.v26644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26644 s i)) at 1.
  unfold R.v26644, N.v26644.
  rewrite ?node_26637.
  rewrite ?node_26638.
  rewrite ?node_26639.
  rewrite ?node_26643.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26645 (s : N.State) (i : N.Inputs) :
  R.v26645 (state s) (inputs i) = Zmod.unsigned (N.v26645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26645 s i)) at 1.
  unfold R.v26645, N.v26645.
  unfold R.v6, N.v6.
  rewrite ?node_26644.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26646 (s : N.State) (i : N.Inputs) :
  R.v26646 (state s) (inputs i) = Zmod.unsigned (N.v26646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26646 s i)) at 1.
  unfold R.v26646, N.v26646.
  rewrite ?node_10172.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26647 (s : N.State) (i : N.Inputs) :
  R.v26647 (state s) (inputs i) = Zmod.unsigned (N.v26647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26647 s i)) at 1.
  unfold R.v26647, N.v26647.
  unfold R.v6, N.v6.
  rewrite ?node_10328.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26648 (s : N.State) (i : N.Inputs) :
  R.v26648 (state s) (inputs i) = Zmod.unsigned (N.v26648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26648 s i)) at 1.
  unfold R.v26648, N.v26648.
  unfold R.v6, N.v6.
  rewrite ?node_10379.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26649 (s : N.State) (i : N.Inputs) :
  R.v26649 (state s) (inputs i) = Zmod.unsigned (N.v26649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26649 s i)) at 1.
  unfold R.v26649, N.v26649.
  rewrite ?node_26646.
  rewrite ?node_26647.
  rewrite ?node_26648.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26650 (s : N.State) (i : N.Inputs) :
  R.v26650 (state s) (inputs i) = Zmod.unsigned (N.v26650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26650 s i)) at 1.
  unfold R.v26650, N.v26650.
  rewrite ?node_26645.
  rewrite ?node_26649.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26651 (s : N.State) (i : N.Inputs) :
  R.v26651 (state s) (inputs i) = Zmod.unsigned (N.v26651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26651 s i)) at 1.
  unfold R.v26651, N.v26651.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26652 (s : N.State) (i : N.Inputs) :
  R.v26652 (state s) (inputs i) = Zmod.unsigned (N.v26652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26652 s i)) at 1.
  unfold R.v26652, N.v26652.
  unfold R.v16463, N.v16463.
  rewrite !state_r1109_nr_5F1109.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1109_nr_5F1109 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26653 (s : N.State) (i : N.Inputs) :
  R.v26653 (state s) (inputs i) = Zmod.unsigned (N.v26653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26653 s i)) at 1.
  unfold R.v26653, N.v26653.
  unfold R.v6, N.v6.
  rewrite !state_r1108_nr_5F1108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1108_nr_5F1108 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26654 (s : N.State) (i : N.Inputs) :
  R.v26654 (state s) (inputs i) = Zmod.unsigned (N.v26654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26654 s i)) at 1.
  unfold R.v26654, N.v26654.
  unfold R.v6, N.v6.
  rewrite !state_r1107_nr_5F1107.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1107_nr_5F1107 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26655 (s : N.State) (i : N.Inputs) :
  R.v26655 (state s) (inputs i) = Zmod.unsigned (N.v26655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26655 s i)) at 1.
  unfold R.v26655, N.v26655.
  rewrite ?node_26653.
  rewrite ?node_26654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26656 (s : N.State) (i : N.Inputs) :
  R.v26656 (state s) (inputs i) = Zmod.unsigned (N.v26656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26656 s i)) at 1.
  unfold R.v26656, N.v26656.
  unfold R.v16484, N.v16484.
  rewrite ?node_26655.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26657 (s : N.State) (i : N.Inputs) :
  R.v26657 (state s) (inputs i) = Zmod.unsigned (N.v26657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26657 s i)) at 1.
  unfold R.v26657, N.v26657.
  rewrite ?node_26652.
  rewrite ?node_26656.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26658 (s : N.State) (i : N.Inputs) :
  R.v26658 (state s) (inputs i) = Zmod.unsigned (N.v26658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26658 s i)) at 1.
  unfold R.v26658, N.v26658.
  unfold R.v6, N.v6.
  rewrite ?node_26657.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26659 (s : N.State) (i : N.Inputs) :
  R.v26659 (state s) (inputs i) = Zmod.unsigned (N.v26659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26659 s i)) at 1.
  unfold R.v26659, N.v26659.
  rewrite ?node_10167.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26660 (s : N.State) (i : N.Inputs) :
  R.v26660 (state s) (inputs i) = Zmod.unsigned (N.v26660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26660 s i)) at 1.
  unfold R.v26660, N.v26660.
  unfold R.v6, N.v6.
  rewrite ?node_10328.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26661 (s : N.State) (i : N.Inputs) :
  R.v26661 (state s) (inputs i) = Zmod.unsigned (N.v26661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26661 s i)) at 1.
  unfold R.v26661, N.v26661.
  rewrite ?node_26659.
  rewrite ?node_26660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26662 (s : N.State) (i : N.Inputs) :
  R.v26662 (state s) (inputs i) = Zmod.unsigned (N.v26662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26662 s i)) at 1.
  unfold R.v26662, N.v26662.
  rewrite ?node_26658.
  rewrite ?node_26661.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26663 (s : N.State) (i : N.Inputs) :
  R.v26663 (state s) (inputs i) = Zmod.unsigned (N.v26663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26663 s i)) at 1.
  unfold R.v26663, N.v26663.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26664 (s : N.State) (i : N.Inputs) :
  R.v26664 (state s) (inputs i) = Zmod.unsigned (N.v26664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26664 s i)) at 1.
  unfold R.v26664, N.v26664.
  rewrite ?node_10171.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26665 (s : N.State) (i : N.Inputs) :
  R.v26665 (state s) (inputs i) = Zmod.unsigned (N.v26665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26665 s i)) at 1.
  unfold R.v26665, N.v26665.
  unfold R.v6, N.v6.
  rewrite !state_r1110_nr_5F1110.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1110_nr_5F1110 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26666 (s : N.State) (i : N.Inputs) :
  R.v26666 (state s) (inputs i) = Zmod.unsigned (N.v26666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26666 s i)) at 1.
  unfold R.v26666, N.v26666.
  unfold R.v6, N.v6.
  rewrite ?node_10167.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26667 (s : N.State) (i : N.Inputs) :
  R.v26667 (state s) (inputs i) = Zmod.unsigned (N.v26667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26667 s i)) at 1.
  unfold R.v26667, N.v26667.
  rewrite ?node_26665.
  rewrite ?node_26666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26668 (s : N.State) (i : N.Inputs) :
  R.v26668 (state s) (inputs i) = Zmod.unsigned (N.v26668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26668 s i)) at 1.
  unfold R.v26668, N.v26668.
  unfold R.v16484, N.v16484.
  rewrite ?node_26667.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26669 (s : N.State) (i : N.Inputs) :
  R.v26669 (state s) (inputs i) = Zmod.unsigned (N.v26669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26669 s i)) at 1.
  unfold R.v26669, N.v26669.
  rewrite ?node_26664.
  rewrite ?node_26668.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26670 (s : N.State) (i : N.Inputs) :
  R.v26670 (state s) (inputs i) = Zmod.unsigned (N.v26670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26670 s i)) at 1.
  unfold R.v26670, N.v26670.
  unfold R.v6, N.v6.
  rewrite ?node_26669.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26671 (s : N.State) (i : N.Inputs) :
  R.v26671 (state s) (inputs i) = Zmod.unsigned (N.v26671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26671 s i)) at 1.
  unfold R.v26671, N.v26671.
  rewrite ?node_10172.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26672 (s : N.State) (i : N.Inputs) :
  R.v26672 (state s) (inputs i) = Zmod.unsigned (N.v26672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26672 s i)) at 1.
  unfold R.v26672, N.v26672.
  unfold R.v6, N.v6.
  rewrite ?node_10379.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26673 (s : N.State) (i : N.Inputs) :
  R.v26673 (state s) (inputs i) = Zmod.unsigned (N.v26673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26673 s i)) at 1.
  unfold R.v26673, N.v26673.
  rewrite ?node_26671.
  rewrite ?node_26672.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26674 (s : N.State) (i : N.Inputs) :
  R.v26674 (state s) (inputs i) = Zmod.unsigned (N.v26674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26674 s i)) at 1.
  unfold R.v26674, N.v26674.
  rewrite ?node_26670.
  rewrite ?node_26673.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26675 (s : N.State) (i : N.Inputs) :
  R.v26675 (state s) (inputs i) = Zmod.unsigned (N.v26675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26675 s i)) at 1.
  unfold R.v26675, N.v26675.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26676 (s : N.State) (i : N.Inputs) :
  R.v26676 (state s) (inputs i) = Zmod.unsigned (N.v26676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26676 s i)) at 1.
  unfold R.v26676, N.v26676.
  rewrite ?node_10179.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26677 (s : N.State) (i : N.Inputs) :
  R.v26677 (state s) (inputs i) = Zmod.unsigned (N.v26677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26677 s i)) at 1.
  unfold R.v26677, N.v26677.
  unfold R.v16463, N.v16463.
  rewrite !state_r1114_nr_5F1114.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1114_nr_5F1114 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26678 (s : N.State) (i : N.Inputs) :
  R.v26678 (state s) (inputs i) = Zmod.unsigned (N.v26678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26678 s i)) at 1.
  unfold R.v26678, N.v26678.
  unfold R.v16463, N.v16463.
  rewrite !state_r1113_nr_5F1113.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1113_nr_5F1113 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26679 (s : N.State) (i : N.Inputs) :
  R.v26679 (state s) (inputs i) = Zmod.unsigned (N.v26679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26679 s i)) at 1.
  unfold R.v26679, N.v26679.
  unfold R.v6, N.v6.
  rewrite !state_r1112_nr_5F1112.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1112_nr_5F1112 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26680 (s : N.State) (i : N.Inputs) :
  R.v26680 (state s) (inputs i) = Zmod.unsigned (N.v26680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26680 s i)) at 1.
  unfold R.v26680, N.v26680.
  unfold R.v6, N.v6.
  rewrite !state_r1111_nr_5F1111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1111_nr_5F1111 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26681 (s : N.State) (i : N.Inputs) :
  R.v26681 (state s) (inputs i) = Zmod.unsigned (N.v26681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26681 s i)) at 1.
  unfold R.v26681, N.v26681.
  rewrite ?node_26679.
  rewrite ?node_26680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26682 (s : N.State) (i : N.Inputs) :
  R.v26682 (state s) (inputs i) = Zmod.unsigned (N.v26682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26682 s i)) at 1.
  unfold R.v26682, N.v26682.
  unfold R.v16484, N.v16484.
  rewrite ?node_26681.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26683 (s : N.State) (i : N.Inputs) :
  R.v26683 (state s) (inputs i) = Zmod.unsigned (N.v26683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26683 s i)) at 1.
  unfold R.v26683, N.v26683.
  rewrite ?node_26676.
  rewrite ?node_26677.
  rewrite ?node_26678.
  rewrite ?node_26682.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26684 (s : N.State) (i : N.Inputs) :
  R.v26684 (state s) (inputs i) = Zmod.unsigned (N.v26684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26684 s i)) at 1.
  unfold R.v26684, N.v26684.
  unfold R.v6, N.v6.
  rewrite ?node_26683.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26685 (s : N.State) (i : N.Inputs) :
  R.v26685 (state s) (inputs i) = Zmod.unsigned (N.v26685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26685 s i)) at 1.
  unfold R.v26685, N.v26685.
  rewrite ?node_10180.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26686 (s : N.State) (i : N.Inputs) :
  R.v26686 (state s) (inputs i) = Zmod.unsigned (N.v26686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26686 s i)) at 1.
  unfold R.v26686, N.v26686.
  unfold R.v6, N.v6.
  rewrite ?node_10336.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26687 (s : N.State) (i : N.Inputs) :
  R.v26687 (state s) (inputs i) = Zmod.unsigned (N.v26687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26687 s i)) at 1.
  unfold R.v26687, N.v26687.
  unfold R.v6, N.v6.
  rewrite ?node_10383.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26688 (s : N.State) (i : N.Inputs) :
  R.v26688 (state s) (inputs i) = Zmod.unsigned (N.v26688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26688 s i)) at 1.
  unfold R.v26688, N.v26688.
  rewrite ?node_26685.
  rewrite ?node_26686.
  rewrite ?node_26687.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26689 (s : N.State) (i : N.Inputs) :
  R.v26689 (state s) (inputs i) = Zmod.unsigned (N.v26689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26689 s i)) at 1.
  unfold R.v26689, N.v26689.
  rewrite ?node_26684.
  rewrite ?node_26688.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26690 (s : N.State) (i : N.Inputs) :
  R.v26690 (state s) (inputs i) = Zmod.unsigned (N.v26690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26690 s i)) at 1.
  unfold R.v26690, N.v26690.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26691 (s : N.State) (i : N.Inputs) :
  R.v26691 (state s) (inputs i) = Zmod.unsigned (N.v26691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26691 s i)) at 1.
  unfold R.v26691, N.v26691.
  unfold R.v16463, N.v16463.
  rewrite !state_r1113_nr_5F1113.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1113_nr_5F1113 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26692 (s : N.State) (i : N.Inputs) :
  R.v26692 (state s) (inputs i) = Zmod.unsigned (N.v26692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26692 s i)) at 1.
  unfold R.v26692, N.v26692.
  unfold R.v6, N.v6.
  rewrite !state_r1112_nr_5F1112.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1112_nr_5F1112 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26693 (s : N.State) (i : N.Inputs) :
  R.v26693 (state s) (inputs i) = Zmod.unsigned (N.v26693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26693 s i)) at 1.
  unfold R.v26693, N.v26693.
  unfold R.v6, N.v6.
  rewrite !state_r1111_nr_5F1111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1111_nr_5F1111 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26694 (s : N.State) (i : N.Inputs) :
  R.v26694 (state s) (inputs i) = Zmod.unsigned (N.v26694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26694 s i)) at 1.
  unfold R.v26694, N.v26694.
  rewrite ?node_26692.
  rewrite ?node_26693.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26695 (s : N.State) (i : N.Inputs) :
  R.v26695 (state s) (inputs i) = Zmod.unsigned (N.v26695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26695 s i)) at 1.
  unfold R.v26695, N.v26695.
  unfold R.v16484, N.v16484.
  rewrite ?node_26694.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26696 (s : N.State) (i : N.Inputs) :
  R.v26696 (state s) (inputs i) = Zmod.unsigned (N.v26696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26696 s i)) at 1.
  unfold R.v26696, N.v26696.
  rewrite ?node_26691.
  rewrite ?node_26695.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26697 (s : N.State) (i : N.Inputs) :
  R.v26697 (state s) (inputs i) = Zmod.unsigned (N.v26697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26697 s i)) at 1.
  unfold R.v26697, N.v26697.
  unfold R.v6, N.v6.
  rewrite ?node_26696.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26698 (s : N.State) (i : N.Inputs) :
  R.v26698 (state s) (inputs i) = Zmod.unsigned (N.v26698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26698 s i)) at 1.
  unfold R.v26698, N.v26698.
  rewrite ?node_10175.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26699 (s : N.State) (i : N.Inputs) :
  R.v26699 (state s) (inputs i) = Zmod.unsigned (N.v26699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26699 s i)) at 1.
  unfold R.v26699, N.v26699.
  unfold R.v6, N.v6.
  rewrite ?node_10336.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26700 (s : N.State) (i : N.Inputs) :
  R.v26700 (state s) (inputs i) = Zmod.unsigned (N.v26700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26700 s i)) at 1.
  unfold R.v26700, N.v26700.
  rewrite ?node_26698.
  rewrite ?node_26699.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26701 (s : N.State) (i : N.Inputs) :
  R.v26701 (state s) (inputs i) = Zmod.unsigned (N.v26701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26701 s i)) at 1.
  unfold R.v26701, N.v26701.
  rewrite ?node_26697.
  rewrite ?node_26700.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26702 (s : N.State) (i : N.Inputs) :
  R.v26702 (state s) (inputs i) = Zmod.unsigned (N.v26702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26702 s i)) at 1.
  unfold R.v26702, N.v26702.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26703 (s : N.State) (i : N.Inputs) :
  R.v26703 (state s) (inputs i) = Zmod.unsigned (N.v26703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26703 s i)) at 1.
  unfold R.v26703, N.v26703.
  rewrite ?node_10179.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26704 (s : N.State) (i : N.Inputs) :
  R.v26704 (state s) (inputs i) = Zmod.unsigned (N.v26704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26704 s i)) at 1.
  unfold R.v26704, N.v26704.
  unfold R.v6, N.v6.
  rewrite !state_r1114_nr_5F1114.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1114_nr_5F1114 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26705 (s : N.State) (i : N.Inputs) :
  R.v26705 (state s) (inputs i) = Zmod.unsigned (N.v26705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26705 s i)) at 1.
  unfold R.v26705, N.v26705.
  unfold R.v6, N.v6.
  rewrite ?node_10175.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26706 (s : N.State) (i : N.Inputs) :
  R.v26706 (state s) (inputs i) = Zmod.unsigned (N.v26706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26706 s i)) at 1.
  unfold R.v26706, N.v26706.
  rewrite ?node_26704.
  rewrite ?node_26705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26707 (s : N.State) (i : N.Inputs) :
  R.v26707 (state s) (inputs i) = Zmod.unsigned (N.v26707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26707 s i)) at 1.
  unfold R.v26707, N.v26707.
  unfold R.v16484, N.v16484.
  rewrite ?node_26706.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26708 (s : N.State) (i : N.Inputs) :
  R.v26708 (state s) (inputs i) = Zmod.unsigned (N.v26708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26708 s i)) at 1.
  unfold R.v26708, N.v26708.
  rewrite ?node_26703.
  rewrite ?node_26707.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26709 (s : N.State) (i : N.Inputs) :
  R.v26709 (state s) (inputs i) = Zmod.unsigned (N.v26709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26709 s i)) at 1.
  unfold R.v26709, N.v26709.
  unfold R.v6, N.v6.
  rewrite ?node_26708.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26710 (s : N.State) (i : N.Inputs) :
  R.v26710 (state s) (inputs i) = Zmod.unsigned (N.v26710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26710 s i)) at 1.
  unfold R.v26710, N.v26710.
  rewrite ?node_10180.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26711 (s : N.State) (i : N.Inputs) :
  R.v26711 (state s) (inputs i) = Zmod.unsigned (N.v26711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26711 s i)) at 1.
  unfold R.v26711, N.v26711.
  unfold R.v6, N.v6.
  rewrite ?node_10383.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26712 (s : N.State) (i : N.Inputs) :
  R.v26712 (state s) (inputs i) = Zmod.unsigned (N.v26712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26712 s i)) at 1.
  unfold R.v26712, N.v26712.
  rewrite ?node_26710.
  rewrite ?node_26711.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26713 (s : N.State) (i : N.Inputs) :
  R.v26713 (state s) (inputs i) = Zmod.unsigned (N.v26713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26713 s i)) at 1.
  unfold R.v26713, N.v26713.
  rewrite ?node_26709.
  rewrite ?node_26712.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26714 (s : N.State) (i : N.Inputs) :
  R.v26714 (state s) (inputs i) = Zmod.unsigned (N.v26714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26714 s i)) at 1.
  unfold R.v26714, N.v26714.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26715 (s : N.State) (i : N.Inputs) :
  R.v26715 (state s) (inputs i) = Zmod.unsigned (N.v26715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26715 s i)) at 1.
  unfold R.v26715, N.v26715.
  rewrite ?node_10187.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26716 (s : N.State) (i : N.Inputs) :
  R.v26716 (state s) (inputs i) = Zmod.unsigned (N.v26716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26716 s i)) at 1.
  unfold R.v26716, N.v26716.
  unfold R.v16463, N.v16463.
  rewrite !state_r1118_nr_5F1118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1118_nr_5F1118 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26717 (s : N.State) (i : N.Inputs) :
  R.v26717 (state s) (inputs i) = Zmod.unsigned (N.v26717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26717 s i)) at 1.
  unfold R.v26717, N.v26717.
  unfold R.v16463, N.v16463.
  rewrite !state_r1117_nr_5F1117.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1117_nr_5F1117 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26718 (s : N.State) (i : N.Inputs) :
  R.v26718 (state s) (inputs i) = Zmod.unsigned (N.v26718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26718 s i)) at 1.
  unfold R.v26718, N.v26718.
  unfold R.v6, N.v6.
  rewrite !state_r1116_nr_5F1116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1116_nr_5F1116 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26719 (s : N.State) (i : N.Inputs) :
  R.v26719 (state s) (inputs i) = Zmod.unsigned (N.v26719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26719 s i)) at 1.
  unfold R.v26719, N.v26719.
  unfold R.v6, N.v6.
  rewrite !state_r1115_nr_5F1115.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1115_nr_5F1115 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26720 (s : N.State) (i : N.Inputs) :
  R.v26720 (state s) (inputs i) = Zmod.unsigned (N.v26720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26720 s i)) at 1.
  unfold R.v26720, N.v26720.
  rewrite ?node_26718.
  rewrite ?node_26719.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26721 (s : N.State) (i : N.Inputs) :
  R.v26721 (state s) (inputs i) = Zmod.unsigned (N.v26721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26721 s i)) at 1.
  unfold R.v26721, N.v26721.
  unfold R.v16484, N.v16484.
  rewrite ?node_26720.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26722 (s : N.State) (i : N.Inputs) :
  R.v26722 (state s) (inputs i) = Zmod.unsigned (N.v26722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26722 s i)) at 1.
  unfold R.v26722, N.v26722.
  rewrite ?node_26715.
  rewrite ?node_26716.
  rewrite ?node_26717.
  rewrite ?node_26721.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26723 (s : N.State) (i : N.Inputs) :
  R.v26723 (state s) (inputs i) = Zmod.unsigned (N.v26723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26723 s i)) at 1.
  unfold R.v26723, N.v26723.
  unfold R.v6, N.v6.
  rewrite ?node_26722.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26724 (s : N.State) (i : N.Inputs) :
  R.v26724 (state s) (inputs i) = Zmod.unsigned (N.v26724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26724 s i)) at 1.
  unfold R.v26724, N.v26724.
  rewrite ?node_10188.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26725 (s : N.State) (i : N.Inputs) :
  R.v26725 (state s) (inputs i) = Zmod.unsigned (N.v26725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26725 s i)) at 1.
  unfold R.v26725, N.v26725.
  unfold R.v6, N.v6.
  rewrite ?node_10344.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26726 (s : N.State) (i : N.Inputs) :
  R.v26726 (state s) (inputs i) = Zmod.unsigned (N.v26726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26726 s i)) at 1.
  unfold R.v26726, N.v26726.
  unfold R.v6, N.v6.
  rewrite ?node_10396.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26727 (s : N.State) (i : N.Inputs) :
  R.v26727 (state s) (inputs i) = Zmod.unsigned (N.v26727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26727 s i)) at 1.
  unfold R.v26727, N.v26727.
  rewrite ?node_26724.
  rewrite ?node_26725.
  rewrite ?node_26726.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26728 (s : N.State) (i : N.Inputs) :
  R.v26728 (state s) (inputs i) = Zmod.unsigned (N.v26728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26728 s i)) at 1.
  unfold R.v26728, N.v26728.
  rewrite ?node_26723.
  rewrite ?node_26727.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26729 (s : N.State) (i : N.Inputs) :
  R.v26729 (state s) (inputs i) = Zmod.unsigned (N.v26729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26729 s i)) at 1.
  unfold R.v26729, N.v26729.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26730 (s : N.State) (i : N.Inputs) :
  R.v26730 (state s) (inputs i) = Zmod.unsigned (N.v26730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26730 s i)) at 1.
  unfold R.v26730, N.v26730.
  unfold R.v16463, N.v16463.
  rewrite !state_r1117_nr_5F1117.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1117_nr_5F1117 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26731 (s : N.State) (i : N.Inputs) :
  R.v26731 (state s) (inputs i) = Zmod.unsigned (N.v26731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26731 s i)) at 1.
  unfold R.v26731, N.v26731.
  unfold R.v6, N.v6.
  rewrite !state_r1116_nr_5F1116.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1116_nr_5F1116 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26732 (s : N.State) (i : N.Inputs) :
  R.v26732 (state s) (inputs i) = Zmod.unsigned (N.v26732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26732 s i)) at 1.
  unfold R.v26732, N.v26732.
  unfold R.v6, N.v6.
  rewrite !state_r1115_nr_5F1115.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1115_nr_5F1115 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26733 (s : N.State) (i : N.Inputs) :
  R.v26733 (state s) (inputs i) = Zmod.unsigned (N.v26733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26733 s i)) at 1.
  unfold R.v26733, N.v26733.
  rewrite ?node_26731.
  rewrite ?node_26732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26734 (s : N.State) (i : N.Inputs) :
  R.v26734 (state s) (inputs i) = Zmod.unsigned (N.v26734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26734 s i)) at 1.
  unfold R.v26734, N.v26734.
  unfold R.v16484, N.v16484.
  rewrite ?node_26733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26735 (s : N.State) (i : N.Inputs) :
  R.v26735 (state s) (inputs i) = Zmod.unsigned (N.v26735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26735 s i)) at 1.
  unfold R.v26735, N.v26735.
  rewrite ?node_26730.
  rewrite ?node_26734.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26736 (s : N.State) (i : N.Inputs) :
  R.v26736 (state s) (inputs i) = Zmod.unsigned (N.v26736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26736 s i)) at 1.
  unfold R.v26736, N.v26736.
  unfold R.v6, N.v6.
  rewrite ?node_26735.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26737 (s : N.State) (i : N.Inputs) :
  R.v26737 (state s) (inputs i) = Zmod.unsigned (N.v26737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26737 s i)) at 1.
  unfold R.v26737, N.v26737.
  rewrite ?node_10183.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26738 (s : N.State) (i : N.Inputs) :
  R.v26738 (state s) (inputs i) = Zmod.unsigned (N.v26738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26738 s i)) at 1.
  unfold R.v26738, N.v26738.
  unfold R.v6, N.v6.
  rewrite ?node_10344.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26739 (s : N.State) (i : N.Inputs) :
  R.v26739 (state s) (inputs i) = Zmod.unsigned (N.v26739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26739 s i)) at 1.
  unfold R.v26739, N.v26739.
  rewrite ?node_26737.
  rewrite ?node_26738.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26740 (s : N.State) (i : N.Inputs) :
  R.v26740 (state s) (inputs i) = Zmod.unsigned (N.v26740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26740 s i)) at 1.
  unfold R.v26740, N.v26740.
  rewrite ?node_26736.
  rewrite ?node_26739.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26741 (s : N.State) (i : N.Inputs) :
  R.v26741 (state s) (inputs i) = Zmod.unsigned (N.v26741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26741 s i)) at 1.
  unfold R.v26741, N.v26741.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26742 (s : N.State) (i : N.Inputs) :
  R.v26742 (state s) (inputs i) = Zmod.unsigned (N.v26742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26742 s i)) at 1.
  unfold R.v26742, N.v26742.
  rewrite ?node_10187.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26743 (s : N.State) (i : N.Inputs) :
  R.v26743 (state s) (inputs i) = Zmod.unsigned (N.v26743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26743 s i)) at 1.
  unfold R.v26743, N.v26743.
  unfold R.v6, N.v6.
  rewrite !state_r1118_nr_5F1118.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1118_nr_5F1118 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26744 (s : N.State) (i : N.Inputs) :
  R.v26744 (state s) (inputs i) = Zmod.unsigned (N.v26744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26744 s i)) at 1.
  unfold R.v26744, N.v26744.
  unfold R.v6, N.v6.
  rewrite ?node_10183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26745 (s : N.State) (i : N.Inputs) :
  R.v26745 (state s) (inputs i) = Zmod.unsigned (N.v26745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26745 s i)) at 1.
  unfold R.v26745, N.v26745.
  rewrite ?node_26743.
  rewrite ?node_26744.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26746 (s : N.State) (i : N.Inputs) :
  R.v26746 (state s) (inputs i) = Zmod.unsigned (N.v26746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26746 s i)) at 1.
  unfold R.v26746, N.v26746.
  unfold R.v16484, N.v16484.
  rewrite ?node_26745.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26747 (s : N.State) (i : N.Inputs) :
  R.v26747 (state s) (inputs i) = Zmod.unsigned (N.v26747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26747 s i)) at 1.
  unfold R.v26747, N.v26747.
  rewrite ?node_26742.
  rewrite ?node_26746.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26748 (s : N.State) (i : N.Inputs) :
  R.v26748 (state s) (inputs i) = Zmod.unsigned (N.v26748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26748 s i)) at 1.
  unfold R.v26748, N.v26748.
  unfold R.v6, N.v6.
  rewrite ?node_26747.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26749 (s : N.State) (i : N.Inputs) :
  R.v26749 (state s) (inputs i) = Zmod.unsigned (N.v26749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26749 s i)) at 1.
  unfold R.v26749, N.v26749.
  rewrite ?node_10188.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26750 (s : N.State) (i : N.Inputs) :
  R.v26750 (state s) (inputs i) = Zmod.unsigned (N.v26750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26750 s i)) at 1.
  unfold R.v26750, N.v26750.
  unfold R.v6, N.v6.
  rewrite ?node_10396.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26751 (s : N.State) (i : N.Inputs) :
  R.v26751 (state s) (inputs i) = Zmod.unsigned (N.v26751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26751 s i)) at 1.
  unfold R.v26751, N.v26751.
  rewrite ?node_26749.
  rewrite ?node_26750.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26752 (s : N.State) (i : N.Inputs) :
  R.v26752 (state s) (inputs i) = Zmod.unsigned (N.v26752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26752 s i)) at 1.
  unfold R.v26752, N.v26752.
  rewrite ?node_26748.
  rewrite ?node_26751.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26753 (s : N.State) (i : N.Inputs) :
  R.v26753 (state s) (inputs i) = Zmod.unsigned (N.v26753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26753 s i)) at 1.
  unfold R.v26753, N.v26753.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26754 (s : N.State) (i : N.Inputs) :
  R.v26754 (state s) (inputs i) = Zmod.unsigned (N.v26754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26754 s i)) at 1.
  unfold R.v26754, N.v26754.
  rewrite ?node_10286.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26755 (s : N.State) (i : N.Inputs) :
  R.v26755 (state s) (inputs i) = Zmod.unsigned (N.v26755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26755 s i)) at 1.
  unfold R.v26755, N.v26755.
  unfold R.v16463, N.v16463.
  rewrite !state_r1123_nr_5F1123.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1123_nr_5F1123 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26756 (s : N.State) (i : N.Inputs) :
  R.v26756 (state s) (inputs i) = Zmod.unsigned (N.v26756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26756 s i)) at 1.
  unfold R.v26756, N.v26756.
  unfold R.v16463, N.v16463.
  rewrite !state_r1122_nr_5F1122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1122_nr_5F1122 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26757 (s : N.State) (i : N.Inputs) :
  R.v26757 (state s) (inputs i) = Zmod.unsigned (N.v26757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26757 s i)) at 1.
  unfold R.v26757, N.v26757.
  unfold R.v6, N.v6.
  rewrite !state_r1121_nr_5F1121.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1121_nr_5F1121 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26758 (s : N.State) (i : N.Inputs) :
  R.v26758 (state s) (inputs i) = Zmod.unsigned (N.v26758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26758 s i)) at 1.
  unfold R.v26758, N.v26758.
  unfold R.v6, N.v6.
  rewrite !state_r1120_nr_5F1120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1120_nr_5F1120 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26759 (s : N.State) (i : N.Inputs) :
  R.v26759 (state s) (inputs i) = Zmod.unsigned (N.v26759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26759 s i)) at 1.
  unfold R.v26759, N.v26759.
  rewrite ?node_26757.
  rewrite ?node_26758.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26760 (s : N.State) (i : N.Inputs) :
  R.v26760 (state s) (inputs i) = Zmod.unsigned (N.v26760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26760 s i)) at 1.
  unfold R.v26760, N.v26760.
  unfold R.v16484, N.v16484.
  rewrite ?node_26759.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26761 (s : N.State) (i : N.Inputs) :
  R.v26761 (state s) (inputs i) = Zmod.unsigned (N.v26761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26761 s i)) at 1.
  unfold R.v26761, N.v26761.
  rewrite ?node_26754.
  rewrite ?node_26755.
  rewrite ?node_26756.
  rewrite ?node_26760.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26762 (s : N.State) (i : N.Inputs) :
  R.v26762 (state s) (inputs i) = Zmod.unsigned (N.v26762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26762 s i)) at 1.
  unfold R.v26762, N.v26762.
  unfold R.v6, N.v6.
  rewrite ?node_26761.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26763 (s : N.State) (i : N.Inputs) :
  R.v26763 (state s) (inputs i) = Zmod.unsigned (N.v26763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26763 s i)) at 1.
  unfold R.v26763, N.v26763.
  rewrite ?node_10287.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26764 (s : N.State) (i : N.Inputs) :
  R.v26764 (state s) (inputs i) = Zmod.unsigned (N.v26764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26764 s i)) at 1.
  unfold R.v26764, N.v26764.
  unfold R.v6, N.v6.
  rewrite ?node_10444.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26765 (s : N.State) (i : N.Inputs) :
  R.v26765 (state s) (inputs i) = Zmod.unsigned (N.v26765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26765 s i)) at 1.
  unfold R.v26765, N.v26765.
  unfold R.v6, N.v6.
  rewrite ?node_10513.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26766 (s : N.State) (i : N.Inputs) :
  R.v26766 (state s) (inputs i) = Zmod.unsigned (N.v26766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26766 s i)) at 1.
  unfold R.v26766, N.v26766.
  rewrite ?node_26763.
  rewrite ?node_26764.
  rewrite ?node_26765.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26767 (s : N.State) (i : N.Inputs) :
  R.v26767 (state s) (inputs i) = Zmod.unsigned (N.v26767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26767 s i)) at 1.
  unfold R.v26767, N.v26767.
  rewrite ?node_26762.
  rewrite ?node_26766.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26768 (s : N.State) (i : N.Inputs) :
  R.v26768 (state s) (inputs i) = Zmod.unsigned (N.v26768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26768 s i)) at 1.
  unfold R.v26768, N.v26768.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26769 (s : N.State) (i : N.Inputs) :
  R.v26769 (state s) (inputs i) = Zmod.unsigned (N.v26769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26769 s i)) at 1.
  unfold R.v26769, N.v26769.
  unfold R.v16463, N.v16463.
  rewrite !state_r1122_nr_5F1122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1122_nr_5F1122 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26770 (s : N.State) (i : N.Inputs) :
  R.v26770 (state s) (inputs i) = Zmod.unsigned (N.v26770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26770 s i)) at 1.
  unfold R.v26770, N.v26770.
  unfold R.v6, N.v6.
  rewrite !state_r1121_nr_5F1121.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1121_nr_5F1121 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26771 (s : N.State) (i : N.Inputs) :
  R.v26771 (state s) (inputs i) = Zmod.unsigned (N.v26771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26771 s i)) at 1.
  unfold R.v26771, N.v26771.
  unfold R.v6, N.v6.
  rewrite !state_r1120_nr_5F1120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1120_nr_5F1120 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26772 (s : N.State) (i : N.Inputs) :
  R.v26772 (state s) (inputs i) = Zmod.unsigned (N.v26772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26772 s i)) at 1.
  unfold R.v26772, N.v26772.
  rewrite ?node_26770.
  rewrite ?node_26771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26773 (s : N.State) (i : N.Inputs) :
  R.v26773 (state s) (inputs i) = Zmod.unsigned (N.v26773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26773 s i)) at 1.
  unfold R.v26773, N.v26773.
  unfold R.v16484, N.v16484.
  rewrite ?node_26772.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26774 (s : N.State) (i : N.Inputs) :
  R.v26774 (state s) (inputs i) = Zmod.unsigned (N.v26774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26774 s i)) at 1.
  unfold R.v26774, N.v26774.
  rewrite ?node_26769.
  rewrite ?node_26773.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26775 (s : N.State) (i : N.Inputs) :
  R.v26775 (state s) (inputs i) = Zmod.unsigned (N.v26775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26775 s i)) at 1.
  unfold R.v26775, N.v26775.
  unfold R.v6, N.v6.
  rewrite ?node_26774.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26776 (s : N.State) (i : N.Inputs) :
  R.v26776 (state s) (inputs i) = Zmod.unsigned (N.v26776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26776 s i)) at 1.
  unfold R.v26776, N.v26776.
  rewrite ?node_10282.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26777 (s : N.State) (i : N.Inputs) :
  R.v26777 (state s) (inputs i) = Zmod.unsigned (N.v26777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26777 s i)) at 1.
  unfold R.v26777, N.v26777.
  unfold R.v6, N.v6.
  rewrite ?node_10444.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26778 (s : N.State) (i : N.Inputs) :
  R.v26778 (state s) (inputs i) = Zmod.unsigned (N.v26778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26778 s i)) at 1.
  unfold R.v26778, N.v26778.
  rewrite ?node_26776.
  rewrite ?node_26777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26779 (s : N.State) (i : N.Inputs) :
  R.v26779 (state s) (inputs i) = Zmod.unsigned (N.v26779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26779 s i)) at 1.
  unfold R.v26779, N.v26779.
  rewrite ?node_26775.
  rewrite ?node_26778.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26780 (s : N.State) (i : N.Inputs) :
  R.v26780 (state s) (inputs i) = Zmod.unsigned (N.v26780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26780 s i)) at 1.
  unfold R.v26780, N.v26780.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26781 (s : N.State) (i : N.Inputs) :
  R.v26781 (state s) (inputs i) = Zmod.unsigned (N.v26781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26781 s i)) at 1.
  unfold R.v26781, N.v26781.
  rewrite ?node_10286.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26782 (s : N.State) (i : N.Inputs) :
  R.v26782 (state s) (inputs i) = Zmod.unsigned (N.v26782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26782 s i)) at 1.
  unfold R.v26782, N.v26782.
  unfold R.v6, N.v6.
  rewrite !state_r1123_nr_5F1123.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1123_nr_5F1123 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26783 (s : N.State) (i : N.Inputs) :
  R.v26783 (state s) (inputs i) = Zmod.unsigned (N.v26783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26783 s i)) at 1.
  unfold R.v26783, N.v26783.
  unfold R.v6, N.v6.
  rewrite ?node_10282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26784 (s : N.State) (i : N.Inputs) :
  R.v26784 (state s) (inputs i) = Zmod.unsigned (N.v26784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26784 s i)) at 1.
  unfold R.v26784, N.v26784.
  rewrite ?node_26782.
  rewrite ?node_26783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26785 (s : N.State) (i : N.Inputs) :
  R.v26785 (state s) (inputs i) = Zmod.unsigned (N.v26785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26785 s i)) at 1.
  unfold R.v26785, N.v26785.
  unfold R.v16484, N.v16484.
  rewrite ?node_26784.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26786 (s : N.State) (i : N.Inputs) :
  R.v26786 (state s) (inputs i) = Zmod.unsigned (N.v26786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26786 s i)) at 1.
  unfold R.v26786, N.v26786.
  rewrite ?node_26781.
  rewrite ?node_26785.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26787 (s : N.State) (i : N.Inputs) :
  R.v26787 (state s) (inputs i) = Zmod.unsigned (N.v26787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26787 s i)) at 1.
  unfold R.v26787, N.v26787.
  unfold R.v6, N.v6.
  rewrite ?node_26786.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26788 (s : N.State) (i : N.Inputs) :
  R.v26788 (state s) (inputs i) = Zmod.unsigned (N.v26788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26788 s i)) at 1.
  unfold R.v26788, N.v26788.
  rewrite ?node_10287.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26789 (s : N.State) (i : N.Inputs) :
  R.v26789 (state s) (inputs i) = Zmod.unsigned (N.v26789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26789 s i)) at 1.
  unfold R.v26789, N.v26789.
  unfold R.v6, N.v6.
  rewrite ?node_10513.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26790 (s : N.State) (i : N.Inputs) :
  R.v26790 (state s) (inputs i) = Zmod.unsigned (N.v26790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26790 s i)) at 1.
  unfold R.v26790, N.v26790.
  rewrite ?node_26788.
  rewrite ?node_26789.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26791 (s : N.State) (i : N.Inputs) :
  R.v26791 (state s) (inputs i) = Zmod.unsigned (N.v26791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26791 s i)) at 1.
  unfold R.v26791, N.v26791.
  rewrite ?node_26787.
  rewrite ?node_26790.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26792 (s : N.State) (i : N.Inputs) :
  R.v26792 (state s) (inputs i) = Zmod.unsigned (N.v26792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26792 s i)) at 1.
  unfold R.v26792, N.v26792.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26793 (s : N.State) (i : N.Inputs) :
  R.v26793 (state s) (inputs i) = Zmod.unsigned (N.v26793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26793 s i)) at 1.
  unfold R.v26793, N.v26793.
  rewrite ?node_10293.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26794 (s : N.State) (i : N.Inputs) :
  R.v26794 (state s) (inputs i) = Zmod.unsigned (N.v26794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26794 s i)) at 1.
  unfold R.v26794, N.v26794.
  unfold R.v16463, N.v16463.
  rewrite !state_r1127_nr_5F1127.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1127_nr_5F1127 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26795 (s : N.State) (i : N.Inputs) :
  R.v26795 (state s) (inputs i) = Zmod.unsigned (N.v26795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26795 s i)) at 1.
  unfold R.v26795, N.v26795.
  unfold R.v16463, N.v16463.
  rewrite !state_r1126_nr_5F1126.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1126_nr_5F1126 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26796 (s : N.State) (i : N.Inputs) :
  R.v26796 (state s) (inputs i) = Zmod.unsigned (N.v26796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26796 s i)) at 1.
  unfold R.v26796, N.v26796.
  unfold R.v6, N.v6.
  rewrite !state_r1125_nr_5F1125.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1125_nr_5F1125 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26797 (s : N.State) (i : N.Inputs) :
  R.v26797 (state s) (inputs i) = Zmod.unsigned (N.v26797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26797 s i)) at 1.
  unfold R.v26797, N.v26797.
  unfold R.v6, N.v6.
  rewrite !state_r1124_nr_5F1124.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1124_nr_5F1124 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26798 (s : N.State) (i : N.Inputs) :
  R.v26798 (state s) (inputs i) = Zmod.unsigned (N.v26798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26798 s i)) at 1.
  unfold R.v26798, N.v26798.
  rewrite ?node_26796.
  rewrite ?node_26797.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26799 (s : N.State) (i : N.Inputs) :
  R.v26799 (state s) (inputs i) = Zmod.unsigned (N.v26799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26799 s i)) at 1.
  unfold R.v26799, N.v26799.
  unfold R.v16484, N.v16484.
  rewrite ?node_26798.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26800 (s : N.State) (i : N.Inputs) :
  R.v26800 (state s) (inputs i) = Zmod.unsigned (N.v26800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26800 s i)) at 1.
  unfold R.v26800, N.v26800.
  rewrite ?node_26793.
  rewrite ?node_26794.
  rewrite ?node_26795.
  rewrite ?node_26799.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26801 (s : N.State) (i : N.Inputs) :
  R.v26801 (state s) (inputs i) = Zmod.unsigned (N.v26801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26801 s i)) at 1.
  unfold R.v26801, N.v26801.
  unfold R.v6, N.v6.
  rewrite ?node_26800.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26802 (s : N.State) (i : N.Inputs) :
  R.v26802 (state s) (inputs i) = Zmod.unsigned (N.v26802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26802 s i)) at 1.
  unfold R.v26802, N.v26802.
  rewrite ?node_10294.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26803 (s : N.State) (i : N.Inputs) :
  R.v26803 (state s) (inputs i) = Zmod.unsigned (N.v26803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26803 s i)) at 1.
  unfold R.v26803, N.v26803.
  unfold R.v6, N.v6.
  rewrite ?node_10451.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26804 (s : N.State) (i : N.Inputs) :
  R.v26804 (state s) (inputs i) = Zmod.unsigned (N.v26804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26804 s i)) at 1.
  unfold R.v26804, N.v26804.
  unfold R.v6, N.v6.
  rewrite ?node_10517.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26805 (s : N.State) (i : N.Inputs) :
  R.v26805 (state s) (inputs i) = Zmod.unsigned (N.v26805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26805 s i)) at 1.
  unfold R.v26805, N.v26805.
  rewrite ?node_26802.
  rewrite ?node_26803.
  rewrite ?node_26804.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26806 (s : N.State) (i : N.Inputs) :
  R.v26806 (state s) (inputs i) = Zmod.unsigned (N.v26806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26806 s i)) at 1.
  unfold R.v26806, N.v26806.
  rewrite ?node_26801.
  rewrite ?node_26805.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26807 (s : N.State) (i : N.Inputs) :
  R.v26807 (state s) (inputs i) = Zmod.unsigned (N.v26807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26807 s i)) at 1.
  unfold R.v26807, N.v26807.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26808 (s : N.State) (i : N.Inputs) :
  R.v26808 (state s) (inputs i) = Zmod.unsigned (N.v26808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26808 s i)) at 1.
  unfold R.v26808, N.v26808.
  unfold R.v16463, N.v16463.
  rewrite !state_r1126_nr_5F1126.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1126_nr_5F1126 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26809 (s : N.State) (i : N.Inputs) :
  R.v26809 (state s) (inputs i) = Zmod.unsigned (N.v26809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26809 s i)) at 1.
  unfold R.v26809, N.v26809.
  unfold R.v6, N.v6.
  rewrite !state_r1125_nr_5F1125.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1125_nr_5F1125 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26810 (s : N.State) (i : N.Inputs) :
  R.v26810 (state s) (inputs i) = Zmod.unsigned (N.v26810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26810 s i)) at 1.
  unfold R.v26810, N.v26810.
  unfold R.v6, N.v6.
  rewrite !state_r1124_nr_5F1124.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1124_nr_5F1124 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26811 (s : N.State) (i : N.Inputs) :
  R.v26811 (state s) (inputs i) = Zmod.unsigned (N.v26811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26811 s i)) at 1.
  unfold R.v26811, N.v26811.
  rewrite ?node_26809.
  rewrite ?node_26810.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26812 (s : N.State) (i : N.Inputs) :
  R.v26812 (state s) (inputs i) = Zmod.unsigned (N.v26812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26812 s i)) at 1.
  unfold R.v26812, N.v26812.
  unfold R.v16484, N.v16484.
  rewrite ?node_26811.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26813 (s : N.State) (i : N.Inputs) :
  R.v26813 (state s) (inputs i) = Zmod.unsigned (N.v26813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26813 s i)) at 1.
  unfold R.v26813, N.v26813.
  rewrite ?node_26808.
  rewrite ?node_26812.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26814 (s : N.State) (i : N.Inputs) :
  R.v26814 (state s) (inputs i) = Zmod.unsigned (N.v26814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26814 s i)) at 1.
  unfold R.v26814, N.v26814.
  unfold R.v6, N.v6.
  rewrite ?node_26813.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26815 (s : N.State) (i : N.Inputs) :
  R.v26815 (state s) (inputs i) = Zmod.unsigned (N.v26815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26815 s i)) at 1.
  unfold R.v26815, N.v26815.
  rewrite ?node_10289.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26816 (s : N.State) (i : N.Inputs) :
  R.v26816 (state s) (inputs i) = Zmod.unsigned (N.v26816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26816 s i)) at 1.
  unfold R.v26816, N.v26816.
  unfold R.v6, N.v6.
  rewrite ?node_10451.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26817 (s : N.State) (i : N.Inputs) :
  R.v26817 (state s) (inputs i) = Zmod.unsigned (N.v26817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26817 s i)) at 1.
  unfold R.v26817, N.v26817.
  rewrite ?node_26815.
  rewrite ?node_26816.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26818 (s : N.State) (i : N.Inputs) :
  R.v26818 (state s) (inputs i) = Zmod.unsigned (N.v26818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26818 s i)) at 1.
  unfold R.v26818, N.v26818.
  rewrite ?node_26814.
  rewrite ?node_26817.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26819 (s : N.State) (i : N.Inputs) :
  R.v26819 (state s) (inputs i) = Zmod.unsigned (N.v26819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26819 s i)) at 1.
  unfold R.v26819, N.v26819.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26820 (s : N.State) (i : N.Inputs) :
  R.v26820 (state s) (inputs i) = Zmod.unsigned (N.v26820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26820 s i)) at 1.
  unfold R.v26820, N.v26820.
  rewrite ?node_10293.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26821 (s : N.State) (i : N.Inputs) :
  R.v26821 (state s) (inputs i) = Zmod.unsigned (N.v26821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26821 s i)) at 1.
  unfold R.v26821, N.v26821.
  unfold R.v6, N.v6.
  rewrite !state_r1127_nr_5F1127.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1127_nr_5F1127 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26822 (s : N.State) (i : N.Inputs) :
  R.v26822 (state s) (inputs i) = Zmod.unsigned (N.v26822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26822 s i)) at 1.
  unfold R.v26822, N.v26822.
  unfold R.v6, N.v6.
  rewrite ?node_10289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26823 (s : N.State) (i : N.Inputs) :
  R.v26823 (state s) (inputs i) = Zmod.unsigned (N.v26823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26823 s i)) at 1.
  unfold R.v26823, N.v26823.
  rewrite ?node_26821.
  rewrite ?node_26822.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26824 (s : N.State) (i : N.Inputs) :
  R.v26824 (state s) (inputs i) = Zmod.unsigned (N.v26824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26824 s i)) at 1.
  unfold R.v26824, N.v26824.
  unfold R.v16484, N.v16484.
  rewrite ?node_26823.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26825 (s : N.State) (i : N.Inputs) :
  R.v26825 (state s) (inputs i) = Zmod.unsigned (N.v26825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26825 s i)) at 1.
  unfold R.v26825, N.v26825.
  rewrite ?node_26820.
  rewrite ?node_26824.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26826 (s : N.State) (i : N.Inputs) :
  R.v26826 (state s) (inputs i) = Zmod.unsigned (N.v26826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26826 s i)) at 1.
  unfold R.v26826, N.v26826.
  unfold R.v6, N.v6.
  rewrite ?node_26825.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26827 (s : N.State) (i : N.Inputs) :
  R.v26827 (state s) (inputs i) = Zmod.unsigned (N.v26827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26827 s i)) at 1.
  unfold R.v26827, N.v26827.
  rewrite ?node_10294.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26828 (s : N.State) (i : N.Inputs) :
  R.v26828 (state s) (inputs i) = Zmod.unsigned (N.v26828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26828 s i)) at 1.
  unfold R.v26828, N.v26828.
  unfold R.v6, N.v6.
  rewrite ?node_10517.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26829 (s : N.State) (i : N.Inputs) :
  R.v26829 (state s) (inputs i) = Zmod.unsigned (N.v26829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26829 s i)) at 1.
  unfold R.v26829, N.v26829.
  rewrite ?node_26827.
  rewrite ?node_26828.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26830 (s : N.State) (i : N.Inputs) :
  R.v26830 (state s) (inputs i) = Zmod.unsigned (N.v26830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26830 s i)) at 1.
  unfold R.v26830, N.v26830.
  rewrite ?node_26826.
  rewrite ?node_26829.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26831 (s : N.State) (i : N.Inputs) :
  R.v26831 (state s) (inputs i) = Zmod.unsigned (N.v26831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26831 s i)) at 1.
  unfold R.v26831, N.v26831.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26832 (s : N.State) (i : N.Inputs) :
  R.v26832 (state s) (inputs i) = Zmod.unsigned (N.v26832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26832 s i)) at 1.
  unfold R.v26832, N.v26832.
  rewrite ?node_10301.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26833 (s : N.State) (i : N.Inputs) :
  R.v26833 (state s) (inputs i) = Zmod.unsigned (N.v26833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26833 s i)) at 1.
  unfold R.v26833, N.v26833.
  unfold R.v16463, N.v16463.
  rewrite !state_r1131_nr_5F1131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1131_nr_5F1131 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26834 (s : N.State) (i : N.Inputs) :
  R.v26834 (state s) (inputs i) = Zmod.unsigned (N.v26834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26834 s i)) at 1.
  unfold R.v26834, N.v26834.
  unfold R.v16463, N.v16463.
  rewrite !state_r1130_nr_5F1130.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1130_nr_5F1130 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26835 (s : N.State) (i : N.Inputs) :
  R.v26835 (state s) (inputs i) = Zmod.unsigned (N.v26835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26835 s i)) at 1.
  unfold R.v26835, N.v26835.
  unfold R.v6, N.v6.
  rewrite !state_r1129_nr_5F1129.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1129_nr_5F1129 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26836 (s : N.State) (i : N.Inputs) :
  R.v26836 (state s) (inputs i) = Zmod.unsigned (N.v26836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26836 s i)) at 1.
  unfold R.v26836, N.v26836.
  unfold R.v6, N.v6.
  rewrite !state_r1128_nr_5F1128.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1128_nr_5F1128 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26837 (s : N.State) (i : N.Inputs) :
  R.v26837 (state s) (inputs i) = Zmod.unsigned (N.v26837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26837 s i)) at 1.
  unfold R.v26837, N.v26837.
  rewrite ?node_26835.
  rewrite ?node_26836.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26838 (s : N.State) (i : N.Inputs) :
  R.v26838 (state s) (inputs i) = Zmod.unsigned (N.v26838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26838 s i)) at 1.
  unfold R.v26838, N.v26838.
  unfold R.v16484, N.v16484.
  rewrite ?node_26837.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26839 (s : N.State) (i : N.Inputs) :
  R.v26839 (state s) (inputs i) = Zmod.unsigned (N.v26839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26839 s i)) at 1.
  unfold R.v26839, N.v26839.
  rewrite ?node_26832.
  rewrite ?node_26833.
  rewrite ?node_26834.
  rewrite ?node_26838.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26840 (s : N.State) (i : N.Inputs) :
  R.v26840 (state s) (inputs i) = Zmod.unsigned (N.v26840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26840 s i)) at 1.
  unfold R.v26840, N.v26840.
  unfold R.v6, N.v6.
  rewrite ?node_26839.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26841 (s : N.State) (i : N.Inputs) :
  R.v26841 (state s) (inputs i) = Zmod.unsigned (N.v26841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26841 s i)) at 1.
  unfold R.v26841, N.v26841.
  rewrite ?node_10302.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26842 (s : N.State) (i : N.Inputs) :
  R.v26842 (state s) (inputs i) = Zmod.unsigned (N.v26842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26842 s i)) at 1.
  unfold R.v26842, N.v26842.
  unfold R.v6, N.v6.
  rewrite ?node_10459.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26843 (s : N.State) (i : N.Inputs) :
  R.v26843 (state s) (inputs i) = Zmod.unsigned (N.v26843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26843 s i)) at 1.
  unfold R.v26843, N.v26843.
  unfold R.v6, N.v6.
  rewrite ?node_10521.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26844 (s : N.State) (i : N.Inputs) :
  R.v26844 (state s) (inputs i) = Zmod.unsigned (N.v26844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26844 s i)) at 1.
  unfold R.v26844, N.v26844.
  rewrite ?node_26841.
  rewrite ?node_26842.
  rewrite ?node_26843.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26845 (s : N.State) (i : N.Inputs) :
  R.v26845 (state s) (inputs i) = Zmod.unsigned (N.v26845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26845 s i)) at 1.
  unfold R.v26845, N.v26845.
  rewrite ?node_26840.
  rewrite ?node_26844.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26846 (s : N.State) (i : N.Inputs) :
  R.v26846 (state s) (inputs i) = Zmod.unsigned (N.v26846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26846 s i)) at 1.
  unfold R.v26846, N.v26846.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26847 (s : N.State) (i : N.Inputs) :
  R.v26847 (state s) (inputs i) = Zmod.unsigned (N.v26847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26847 s i)) at 1.
  unfold R.v26847, N.v26847.
  unfold R.v16463, N.v16463.
  rewrite !state_r1130_nr_5F1130.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1130_nr_5F1130 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26848 (s : N.State) (i : N.Inputs) :
  R.v26848 (state s) (inputs i) = Zmod.unsigned (N.v26848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26848 s i)) at 1.
  unfold R.v26848, N.v26848.
  unfold R.v6, N.v6.
  rewrite !state_r1129_nr_5F1129.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1129_nr_5F1129 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26849 (s : N.State) (i : N.Inputs) :
  R.v26849 (state s) (inputs i) = Zmod.unsigned (N.v26849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26849 s i)) at 1.
  unfold R.v26849, N.v26849.
  unfold R.v6, N.v6.
  rewrite !state_r1128_nr_5F1128.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1128_nr_5F1128 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26850 (s : N.State) (i : N.Inputs) :
  R.v26850 (state s) (inputs i) = Zmod.unsigned (N.v26850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26850 s i)) at 1.
  unfold R.v26850, N.v26850.
  rewrite ?node_26848.
  rewrite ?node_26849.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26851 (s : N.State) (i : N.Inputs) :
  R.v26851 (state s) (inputs i) = Zmod.unsigned (N.v26851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26851 s i)) at 1.
  unfold R.v26851, N.v26851.
  unfold R.v16484, N.v16484.
  rewrite ?node_26850.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26852 (s : N.State) (i : N.Inputs) :
  R.v26852 (state s) (inputs i) = Zmod.unsigned (N.v26852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26852 s i)) at 1.
  unfold R.v26852, N.v26852.
  rewrite ?node_26847.
  rewrite ?node_26851.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26853 (s : N.State) (i : N.Inputs) :
  R.v26853 (state s) (inputs i) = Zmod.unsigned (N.v26853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26853 s i)) at 1.
  unfold R.v26853, N.v26853.
  unfold R.v6, N.v6.
  rewrite ?node_26852.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26854 (s : N.State) (i : N.Inputs) :
  R.v26854 (state s) (inputs i) = Zmod.unsigned (N.v26854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26854 s i)) at 1.
  unfold R.v26854, N.v26854.
  rewrite ?node_10297.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26855 (s : N.State) (i : N.Inputs) :
  R.v26855 (state s) (inputs i) = Zmod.unsigned (N.v26855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26855 s i)) at 1.
  unfold R.v26855, N.v26855.
  unfold R.v6, N.v6.
  rewrite ?node_10459.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26856 (s : N.State) (i : N.Inputs) :
  R.v26856 (state s) (inputs i) = Zmod.unsigned (N.v26856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26856 s i)) at 1.
  unfold R.v26856, N.v26856.
  rewrite ?node_26854.
  rewrite ?node_26855.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26857 (s : N.State) (i : N.Inputs) :
  R.v26857 (state s) (inputs i) = Zmod.unsigned (N.v26857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26857 s i)) at 1.
  unfold R.v26857, N.v26857.
  rewrite ?node_26853.
  rewrite ?node_26856.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26858 (s : N.State) (i : N.Inputs) :
  R.v26858 (state s) (inputs i) = Zmod.unsigned (N.v26858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26858 s i)) at 1.
  unfold R.v26858, N.v26858.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26859 (s : N.State) (i : N.Inputs) :
  R.v26859 (state s) (inputs i) = Zmod.unsigned (N.v26859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26859 s i)) at 1.
  unfold R.v26859, N.v26859.
  rewrite ?node_10301.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26860 (s : N.State) (i : N.Inputs) :
  R.v26860 (state s) (inputs i) = Zmod.unsigned (N.v26860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26860 s i)) at 1.
  unfold R.v26860, N.v26860.
  unfold R.v6, N.v6.
  rewrite !state_r1131_nr_5F1131.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1131_nr_5F1131 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26861 (s : N.State) (i : N.Inputs) :
  R.v26861 (state s) (inputs i) = Zmod.unsigned (N.v26861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26861 s i)) at 1.
  unfold R.v26861, N.v26861.
  unfold R.v6, N.v6.
  rewrite ?node_10297.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26862 (s : N.State) (i : N.Inputs) :
  R.v26862 (state s) (inputs i) = Zmod.unsigned (N.v26862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26862 s i)) at 1.
  unfold R.v26862, N.v26862.
  rewrite ?node_26860.
  rewrite ?node_26861.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26863 (s : N.State) (i : N.Inputs) :
  R.v26863 (state s) (inputs i) = Zmod.unsigned (N.v26863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26863 s i)) at 1.
  unfold R.v26863, N.v26863.
  unfold R.v16484, N.v16484.
  rewrite ?node_26862.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26864 (s : N.State) (i : N.Inputs) :
  R.v26864 (state s) (inputs i) = Zmod.unsigned (N.v26864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26864 s i)) at 1.
  unfold R.v26864, N.v26864.
  rewrite ?node_26859.
  rewrite ?node_26863.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26865 (s : N.State) (i : N.Inputs) :
  R.v26865 (state s) (inputs i) = Zmod.unsigned (N.v26865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26865 s i)) at 1.
  unfold R.v26865, N.v26865.
  unfold R.v6, N.v6.
  rewrite ?node_26864.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26866 (s : N.State) (i : N.Inputs) :
  R.v26866 (state s) (inputs i) = Zmod.unsigned (N.v26866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26866 s i)) at 1.
  unfold R.v26866, N.v26866.
  rewrite ?node_10302.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26867 (s : N.State) (i : N.Inputs) :
  R.v26867 (state s) (inputs i) = Zmod.unsigned (N.v26867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26867 s i)) at 1.
  unfold R.v26867, N.v26867.
  unfold R.v6, N.v6.
  rewrite ?node_10521.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26868 (s : N.State) (i : N.Inputs) :
  R.v26868 (state s) (inputs i) = Zmod.unsigned (N.v26868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26868 s i)) at 1.
  unfold R.v26868, N.v26868.
  rewrite ?node_26866.
  rewrite ?node_26867.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26869 (s : N.State) (i : N.Inputs) :
  R.v26869 (state s) (inputs i) = Zmod.unsigned (N.v26869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26869 s i)) at 1.
  unfold R.v26869, N.v26869.
  rewrite ?node_26865.
  rewrite ?node_26868.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26870 (s : N.State) (i : N.Inputs) :
  R.v26870 (state s) (inputs i) = Zmod.unsigned (N.v26870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26870 s i)) at 1.
  unfold R.v26870, N.v26870.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26871 (s : N.State) (i : N.Inputs) :
  R.v26871 (state s) (inputs i) = Zmod.unsigned (N.v26871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26871 s i)) at 1.
  unfold R.v26871, N.v26871.
  rewrite ?node_10309.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26872 (s : N.State) (i : N.Inputs) :
  R.v26872 (state s) (inputs i) = Zmod.unsigned (N.v26872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26872 s i)) at 1.
  unfold R.v26872, N.v26872.
  unfold R.v16463, N.v16463.
  rewrite !state_r1135_nr_5F1135.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1135_nr_5F1135 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26873 (s : N.State) (i : N.Inputs) :
  R.v26873 (state s) (inputs i) = Zmod.unsigned (N.v26873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26873 s i)) at 1.
  unfold R.v26873, N.v26873.
  unfold R.v16463, N.v16463.
  rewrite !state_r1134_nr_5F1134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1134_nr_5F1134 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26874 (s : N.State) (i : N.Inputs) :
  R.v26874 (state s) (inputs i) = Zmod.unsigned (N.v26874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26874 s i)) at 1.
  unfold R.v26874, N.v26874.
  unfold R.v6, N.v6.
  rewrite !state_r1133_nr_5F1133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1133_nr_5F1133 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26875 (s : N.State) (i : N.Inputs) :
  R.v26875 (state s) (inputs i) = Zmod.unsigned (N.v26875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26875 s i)) at 1.
  unfold R.v26875, N.v26875.
  unfold R.v6, N.v6.
  rewrite !state_r1132_nr_5F1132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1132_nr_5F1132 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26876 (s : N.State) (i : N.Inputs) :
  R.v26876 (state s) (inputs i) = Zmod.unsigned (N.v26876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26876 s i)) at 1.
  unfold R.v26876, N.v26876.
  rewrite ?node_26874.
  rewrite ?node_26875.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26877 (s : N.State) (i : N.Inputs) :
  R.v26877 (state s) (inputs i) = Zmod.unsigned (N.v26877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26877 s i)) at 1.
  unfold R.v26877, N.v26877.
  unfold R.v16484, N.v16484.
  rewrite ?node_26876.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26878 (s : N.State) (i : N.Inputs) :
  R.v26878 (state s) (inputs i) = Zmod.unsigned (N.v26878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26878 s i)) at 1.
  unfold R.v26878, N.v26878.
  rewrite ?node_26871.
  rewrite ?node_26872.
  rewrite ?node_26873.
  rewrite ?node_26877.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26879 (s : N.State) (i : N.Inputs) :
  R.v26879 (state s) (inputs i) = Zmod.unsigned (N.v26879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26879 s i)) at 1.
  unfold R.v26879, N.v26879.
  unfold R.v6, N.v6.
  rewrite ?node_26878.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26880 (s : N.State) (i : N.Inputs) :
  R.v26880 (state s) (inputs i) = Zmod.unsigned (N.v26880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26880 s i)) at 1.
  unfold R.v26880, N.v26880.
  rewrite ?node_10310.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26881 (s : N.State) (i : N.Inputs) :
  R.v26881 (state s) (inputs i) = Zmod.unsigned (N.v26881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26881 s i)) at 1.
  unfold R.v26881, N.v26881.
  unfold R.v6, N.v6.
  rewrite ?node_10467.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26882 (s : N.State) (i : N.Inputs) :
  R.v26882 (state s) (inputs i) = Zmod.unsigned (N.v26882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26882 s i)) at 1.
  unfold R.v26882, N.v26882.
  unfold R.v6, N.v6.
  rewrite ?node_10530.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26883 (s : N.State) (i : N.Inputs) :
  R.v26883 (state s) (inputs i) = Zmod.unsigned (N.v26883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26883 s i)) at 1.
  unfold R.v26883, N.v26883.
  rewrite ?node_26880.
  rewrite ?node_26881.
  rewrite ?node_26882.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26884 (s : N.State) (i : N.Inputs) :
  R.v26884 (state s) (inputs i) = Zmod.unsigned (N.v26884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26884 s i)) at 1.
  unfold R.v26884, N.v26884.
  rewrite ?node_26879.
  rewrite ?node_26883.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26885 (s : N.State) (i : N.Inputs) :
  R.v26885 (state s) (inputs i) = Zmod.unsigned (N.v26885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26885 s i)) at 1.
  unfold R.v26885, N.v26885.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26886 (s : N.State) (i : N.Inputs) :
  R.v26886 (state s) (inputs i) = Zmod.unsigned (N.v26886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26886 s i)) at 1.
  unfold R.v26886, N.v26886.
  unfold R.v16463, N.v16463.
  rewrite !state_r1134_nr_5F1134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1134_nr_5F1134 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26887 (s : N.State) (i : N.Inputs) :
  R.v26887 (state s) (inputs i) = Zmod.unsigned (N.v26887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26887 s i)) at 1.
  unfold R.v26887, N.v26887.
  unfold R.v6, N.v6.
  rewrite !state_r1133_nr_5F1133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1133_nr_5F1133 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26888 (s : N.State) (i : N.Inputs) :
  R.v26888 (state s) (inputs i) = Zmod.unsigned (N.v26888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26888 s i)) at 1.
  unfold R.v26888, N.v26888.
  unfold R.v6, N.v6.
  rewrite !state_r1132_nr_5F1132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1132_nr_5F1132 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26889 (s : N.State) (i : N.Inputs) :
  R.v26889 (state s) (inputs i) = Zmod.unsigned (N.v26889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26889 s i)) at 1.
  unfold R.v26889, N.v26889.
  rewrite ?node_26887.
  rewrite ?node_26888.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26890 (s : N.State) (i : N.Inputs) :
  R.v26890 (state s) (inputs i) = Zmod.unsigned (N.v26890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26890 s i)) at 1.
  unfold R.v26890, N.v26890.
  unfold R.v16484, N.v16484.
  rewrite ?node_26889.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26891 (s : N.State) (i : N.Inputs) :
  R.v26891 (state s) (inputs i) = Zmod.unsigned (N.v26891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26891 s i)) at 1.
  unfold R.v26891, N.v26891.
  rewrite ?node_26886.
  rewrite ?node_26890.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26892 (s : N.State) (i : N.Inputs) :
  R.v26892 (state s) (inputs i) = Zmod.unsigned (N.v26892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26892 s i)) at 1.
  unfold R.v26892, N.v26892.
  unfold R.v6, N.v6.
  rewrite ?node_26891.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26893 (s : N.State) (i : N.Inputs) :
  R.v26893 (state s) (inputs i) = Zmod.unsigned (N.v26893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26893 s i)) at 1.
  unfold R.v26893, N.v26893.
  rewrite ?node_10305.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26894 (s : N.State) (i : N.Inputs) :
  R.v26894 (state s) (inputs i) = Zmod.unsigned (N.v26894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26894 s i)) at 1.
  unfold R.v26894, N.v26894.
  unfold R.v6, N.v6.
  rewrite ?node_10467.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26895 (s : N.State) (i : N.Inputs) :
  R.v26895 (state s) (inputs i) = Zmod.unsigned (N.v26895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26895 s i)) at 1.
  unfold R.v26895, N.v26895.
  rewrite ?node_26893.
  rewrite ?node_26894.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26896 (s : N.State) (i : N.Inputs) :
  R.v26896 (state s) (inputs i) = Zmod.unsigned (N.v26896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26896 s i)) at 1.
  unfold R.v26896, N.v26896.
  rewrite ?node_26892.
  rewrite ?node_26895.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26897 (s : N.State) (i : N.Inputs) :
  R.v26897 (state s) (inputs i) = Zmod.unsigned (N.v26897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26897 s i)) at 1.
  unfold R.v26897, N.v26897.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26898 (s : N.State) (i : N.Inputs) :
  R.v26898 (state s) (inputs i) = Zmod.unsigned (N.v26898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26898 s i)) at 1.
  unfold R.v26898, N.v26898.
  rewrite ?node_10309.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26899 (s : N.State) (i : N.Inputs) :
  R.v26899 (state s) (inputs i) = Zmod.unsigned (N.v26899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26899 s i)) at 1.
  unfold R.v26899, N.v26899.
  unfold R.v6, N.v6.
  rewrite !state_r1135_nr_5F1135.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1135_nr_5F1135 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26900 (s : N.State) (i : N.Inputs) :
  R.v26900 (state s) (inputs i) = Zmod.unsigned (N.v26900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26900 s i)) at 1.
  unfold R.v26900, N.v26900.
  unfold R.v6, N.v6.
  rewrite ?node_10305.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26901 (s : N.State) (i : N.Inputs) :
  R.v26901 (state s) (inputs i) = Zmod.unsigned (N.v26901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26901 s i)) at 1.
  unfold R.v26901, N.v26901.
  rewrite ?node_26899.
  rewrite ?node_26900.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26902 (s : N.State) (i : N.Inputs) :
  R.v26902 (state s) (inputs i) = Zmod.unsigned (N.v26902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26902 s i)) at 1.
  unfold R.v26902, N.v26902.
  unfold R.v16484, N.v16484.
  rewrite ?node_26901.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26903 (s : N.State) (i : N.Inputs) :
  R.v26903 (state s) (inputs i) = Zmod.unsigned (N.v26903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26903 s i)) at 1.
  unfold R.v26903, N.v26903.
  rewrite ?node_26898.
  rewrite ?node_26902.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26904 (s : N.State) (i : N.Inputs) :
  R.v26904 (state s) (inputs i) = Zmod.unsigned (N.v26904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26904 s i)) at 1.
  unfold R.v26904, N.v26904.
  unfold R.v6, N.v6.
  rewrite ?node_26903.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26905 (s : N.State) (i : N.Inputs) :
  R.v26905 (state s) (inputs i) = Zmod.unsigned (N.v26905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26905 s i)) at 1.
  unfold R.v26905, N.v26905.
  rewrite ?node_10310.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26906 (s : N.State) (i : N.Inputs) :
  R.v26906 (state s) (inputs i) = Zmod.unsigned (N.v26906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26906 s i)) at 1.
  unfold R.v26906, N.v26906.
  unfold R.v6, N.v6.
  rewrite ?node_10530.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26907 (s : N.State) (i : N.Inputs) :
  R.v26907 (state s) (inputs i) = Zmod.unsigned (N.v26907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26907 s i)) at 1.
  unfold R.v26907, N.v26907.
  rewrite ?node_26905.
  rewrite ?node_26906.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26908 (s : N.State) (i : N.Inputs) :
  R.v26908 (state s) (inputs i) = Zmod.unsigned (N.v26908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26908 s i)) at 1.
  unfold R.v26908, N.v26908.
  rewrite ?node_26904.
  rewrite ?node_26907.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26909 (s : N.State) (i : N.Inputs) :
  R.v26909 (state s) (inputs i) = Zmod.unsigned (N.v26909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26909 s i)) at 1.
  unfold R.v26909, N.v26909.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26910 (s : N.State) (i : N.Inputs) :
  R.v26910 (state s) (inputs i) = Zmod.unsigned (N.v26910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26910 s i)) at 1.
  unfold R.v26910, N.v26910.
  rewrite ?node_10321.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26911 (s : N.State) (i : N.Inputs) :
  R.v26911 (state s) (inputs i) = Zmod.unsigned (N.v26911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26911 s i)) at 1.
  unfold R.v26911, N.v26911.
  unfold R.v16463, N.v16463.
  rewrite !state_r1139_nr_5F1139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1139_nr_5F1139 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26912 (s : N.State) (i : N.Inputs) :
  R.v26912 (state s) (inputs i) = Zmod.unsigned (N.v26912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26912 s i)) at 1.
  unfold R.v26912, N.v26912.
  unfold R.v16463, N.v16463.
  rewrite !state_r1138_nr_5F1138.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1138_nr_5F1138 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26913 (s : N.State) (i : N.Inputs) :
  R.v26913 (state s) (inputs i) = Zmod.unsigned (N.v26913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26913 s i)) at 1.
  unfold R.v26913, N.v26913.
  unfold R.v6, N.v6.
  rewrite !state_r1137_nr_5F1137.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1137_nr_5F1137 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26914 (s : N.State) (i : N.Inputs) :
  R.v26914 (state s) (inputs i) = Zmod.unsigned (N.v26914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26914 s i)) at 1.
  unfold R.v26914, N.v26914.
  unfold R.v6, N.v6.
  rewrite !state_r1136_nr_5F1136.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1136_nr_5F1136 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26915 (s : N.State) (i : N.Inputs) :
  R.v26915 (state s) (inputs i) = Zmod.unsigned (N.v26915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26915 s i)) at 1.
  unfold R.v26915, N.v26915.
  rewrite ?node_26913.
  rewrite ?node_26914.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26916 (s : N.State) (i : N.Inputs) :
  R.v26916 (state s) (inputs i) = Zmod.unsigned (N.v26916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26916 s i)) at 1.
  unfold R.v26916, N.v26916.
  unfold R.v16484, N.v16484.
  rewrite ?node_26915.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26917 (s : N.State) (i : N.Inputs) :
  R.v26917 (state s) (inputs i) = Zmod.unsigned (N.v26917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26917 s i)) at 1.
  unfold R.v26917, N.v26917.
  rewrite ?node_26910.
  rewrite ?node_26911.
  rewrite ?node_26912.
  rewrite ?node_26916.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26918 (s : N.State) (i : N.Inputs) :
  R.v26918 (state s) (inputs i) = Zmod.unsigned (N.v26918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26918 s i)) at 1.
  unfold R.v26918, N.v26918.
  unfold R.v6, N.v6.
  rewrite ?node_26917.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26919 (s : N.State) (i : N.Inputs) :
  R.v26919 (state s) (inputs i) = Zmod.unsigned (N.v26919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26919 s i)) at 1.
  unfold R.v26919, N.v26919.
  rewrite ?node_10322.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26920 (s : N.State) (i : N.Inputs) :
  R.v26920 (state s) (inputs i) = Zmod.unsigned (N.v26920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26920 s i)) at 1.
  unfold R.v26920, N.v26920.
  unfold R.v6, N.v6.
  rewrite ?node_10479.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26921 (s : N.State) (i : N.Inputs) :
  R.v26921 (state s) (inputs i) = Zmod.unsigned (N.v26921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26921 s i)) at 1.
  unfold R.v26921, N.v26921.
  unfold R.v6, N.v6.
  rewrite ?node_10533.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26922 (s : N.State) (i : N.Inputs) :
  R.v26922 (state s) (inputs i) = Zmod.unsigned (N.v26922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26922 s i)) at 1.
  unfold R.v26922, N.v26922.
  rewrite ?node_26919.
  rewrite ?node_26920.
  rewrite ?node_26921.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26923 (s : N.State) (i : N.Inputs) :
  R.v26923 (state s) (inputs i) = Zmod.unsigned (N.v26923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26923 s i)) at 1.
  unfold R.v26923, N.v26923.
  rewrite ?node_26918.
  rewrite ?node_26922.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26924 (s : N.State) (i : N.Inputs) :
  R.v26924 (state s) (inputs i) = Zmod.unsigned (N.v26924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26924 s i)) at 1.
  unfold R.v26924, N.v26924.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26925 (s : N.State) (i : N.Inputs) :
  R.v26925 (state s) (inputs i) = Zmod.unsigned (N.v26925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26925 s i)) at 1.
  unfold R.v26925, N.v26925.
  unfold R.v16463, N.v16463.
  rewrite !state_r1138_nr_5F1138.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1138_nr_5F1138 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26926 (s : N.State) (i : N.Inputs) :
  R.v26926 (state s) (inputs i) = Zmod.unsigned (N.v26926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26926 s i)) at 1.
  unfold R.v26926, N.v26926.
  unfold R.v6, N.v6.
  rewrite !state_r1137_nr_5F1137.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1137_nr_5F1137 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26927 (s : N.State) (i : N.Inputs) :
  R.v26927 (state s) (inputs i) = Zmod.unsigned (N.v26927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26927 s i)) at 1.
  unfold R.v26927, N.v26927.
  unfold R.v6, N.v6.
  rewrite !state_r1136_nr_5F1136.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1136_nr_5F1136 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26928 (s : N.State) (i : N.Inputs) :
  R.v26928 (state s) (inputs i) = Zmod.unsigned (N.v26928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26928 s i)) at 1.
  unfold R.v26928, N.v26928.
  rewrite ?node_26926.
  rewrite ?node_26927.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26929 (s : N.State) (i : N.Inputs) :
  R.v26929 (state s) (inputs i) = Zmod.unsigned (N.v26929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26929 s i)) at 1.
  unfold R.v26929, N.v26929.
  unfold R.v16484, N.v16484.
  rewrite ?node_26928.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26930 (s : N.State) (i : N.Inputs) :
  R.v26930 (state s) (inputs i) = Zmod.unsigned (N.v26930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26930 s i)) at 1.
  unfold R.v26930, N.v26930.
  rewrite ?node_26925.
  rewrite ?node_26929.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26931 (s : N.State) (i : N.Inputs) :
  R.v26931 (state s) (inputs i) = Zmod.unsigned (N.v26931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26931 s i)) at 1.
  unfold R.v26931, N.v26931.
  unfold R.v6, N.v6.
  rewrite ?node_26930.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26932 (s : N.State) (i : N.Inputs) :
  R.v26932 (state s) (inputs i) = Zmod.unsigned (N.v26932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26932 s i)) at 1.
  unfold R.v26932, N.v26932.
  rewrite ?node_10317.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26933 (s : N.State) (i : N.Inputs) :
  R.v26933 (state s) (inputs i) = Zmod.unsigned (N.v26933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26933 s i)) at 1.
  unfold R.v26933, N.v26933.
  unfold R.v6, N.v6.
  rewrite ?node_10479.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26934 (s : N.State) (i : N.Inputs) :
  R.v26934 (state s) (inputs i) = Zmod.unsigned (N.v26934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26934 s i)) at 1.
  unfold R.v26934, N.v26934.
  rewrite ?node_26932.
  rewrite ?node_26933.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26935 (s : N.State) (i : N.Inputs) :
  R.v26935 (state s) (inputs i) = Zmod.unsigned (N.v26935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26935 s i)) at 1.
  unfold R.v26935, N.v26935.
  rewrite ?node_26931.
  rewrite ?node_26934.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26936 (s : N.State) (i : N.Inputs) :
  R.v26936 (state s) (inputs i) = Zmod.unsigned (N.v26936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26936 s i)) at 1.
  unfold R.v26936, N.v26936.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26937 (s : N.State) (i : N.Inputs) :
  R.v26937 (state s) (inputs i) = Zmod.unsigned (N.v26937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26937 s i)) at 1.
  unfold R.v26937, N.v26937.
  rewrite ?node_10321.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26938 (s : N.State) (i : N.Inputs) :
  R.v26938 (state s) (inputs i) = Zmod.unsigned (N.v26938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26938 s i)) at 1.
  unfold R.v26938, N.v26938.
  unfold R.v6, N.v6.
  rewrite !state_r1139_nr_5F1139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1139_nr_5F1139 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26939 (s : N.State) (i : N.Inputs) :
  R.v26939 (state s) (inputs i) = Zmod.unsigned (N.v26939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26939 s i)) at 1.
  unfold R.v26939, N.v26939.
  unfold R.v6, N.v6.
  rewrite ?node_10317.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26940 (s : N.State) (i : N.Inputs) :
  R.v26940 (state s) (inputs i) = Zmod.unsigned (N.v26940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26940 s i)) at 1.
  unfold R.v26940, N.v26940.
  rewrite ?node_26938.
  rewrite ?node_26939.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26941 (s : N.State) (i : N.Inputs) :
  R.v26941 (state s) (inputs i) = Zmod.unsigned (N.v26941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26941 s i)) at 1.
  unfold R.v26941, N.v26941.
  unfold R.v16484, N.v16484.
  rewrite ?node_26940.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26942 (s : N.State) (i : N.Inputs) :
  R.v26942 (state s) (inputs i) = Zmod.unsigned (N.v26942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26942 s i)) at 1.
  unfold R.v26942, N.v26942.
  rewrite ?node_26937.
  rewrite ?node_26941.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26943 (s : N.State) (i : N.Inputs) :
  R.v26943 (state s) (inputs i) = Zmod.unsigned (N.v26943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26943 s i)) at 1.
  unfold R.v26943, N.v26943.
  unfold R.v6, N.v6.
  rewrite ?node_26942.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26944 (s : N.State) (i : N.Inputs) :
  R.v26944 (state s) (inputs i) = Zmod.unsigned (N.v26944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26944 s i)) at 1.
  unfold R.v26944, N.v26944.
  rewrite ?node_10322.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26945 (s : N.State) (i : N.Inputs) :
  R.v26945 (state s) (inputs i) = Zmod.unsigned (N.v26945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26945 s i)) at 1.
  unfold R.v26945, N.v26945.
  unfold R.v6, N.v6.
  rewrite ?node_10533.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26946 (s : N.State) (i : N.Inputs) :
  R.v26946 (state s) (inputs i) = Zmod.unsigned (N.v26946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26946 s i)) at 1.
  unfold R.v26946, N.v26946.
  rewrite ?node_26944.
  rewrite ?node_26945.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26947 (s : N.State) (i : N.Inputs) :
  R.v26947 (state s) (inputs i) = Zmod.unsigned (N.v26947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26947 s i)) at 1.
  unfold R.v26947, N.v26947.
  rewrite ?node_26943.
  rewrite ?node_26946.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26948 (s : N.State) (i : N.Inputs) :
  R.v26948 (state s) (inputs i) = Zmod.unsigned (N.v26948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26948 s i)) at 1.
  unfold R.v26948, N.v26948.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26949 (s : N.State) (i : N.Inputs) :
  R.v26949 (state s) (inputs i) = Zmod.unsigned (N.v26949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26949 s i)) at 1.
  unfold R.v26949, N.v26949.
  rewrite ?node_10328.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26950 (s : N.State) (i : N.Inputs) :
  R.v26950 (state s) (inputs i) = Zmod.unsigned (N.v26950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26950 s i)) at 1.
  unfold R.v26950, N.v26950.
  unfold R.v16463, N.v16463.
  rewrite !state_r1143_nr_5F1143.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1143_nr_5F1143 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26951 (s : N.State) (i : N.Inputs) :
  R.v26951 (state s) (inputs i) = Zmod.unsigned (N.v26951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26951 s i)) at 1.
  unfold R.v26951, N.v26951.
  unfold R.v16463, N.v16463.
  rewrite !state_r1142_nr_5F1142.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1142_nr_5F1142 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26952 (s : N.State) (i : N.Inputs) :
  R.v26952 (state s) (inputs i) = Zmod.unsigned (N.v26952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26952 s i)) at 1.
  unfold R.v26952, N.v26952.
  unfold R.v6, N.v6.
  rewrite !state_r1141_nr_5F1141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1141_nr_5F1141 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26953 (s : N.State) (i : N.Inputs) :
  R.v26953 (state s) (inputs i) = Zmod.unsigned (N.v26953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26953 s i)) at 1.
  unfold R.v26953, N.v26953.
  unfold R.v6, N.v6.
  rewrite !state_r1140_nr_5F1140.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1140_nr_5F1140 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26954 (s : N.State) (i : N.Inputs) :
  R.v26954 (state s) (inputs i) = Zmod.unsigned (N.v26954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26954 s i)) at 1.
  unfold R.v26954, N.v26954.
  rewrite ?node_26952.
  rewrite ?node_26953.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26955 (s : N.State) (i : N.Inputs) :
  R.v26955 (state s) (inputs i) = Zmod.unsigned (N.v26955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26955 s i)) at 1.
  unfold R.v26955, N.v26955.
  unfold R.v16484, N.v16484.
  rewrite ?node_26954.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26956 (s : N.State) (i : N.Inputs) :
  R.v26956 (state s) (inputs i) = Zmod.unsigned (N.v26956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26956 s i)) at 1.
  unfold R.v26956, N.v26956.
  rewrite ?node_26949.
  rewrite ?node_26950.
  rewrite ?node_26951.
  rewrite ?node_26955.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26957 (s : N.State) (i : N.Inputs) :
  R.v26957 (state s) (inputs i) = Zmod.unsigned (N.v26957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26957 s i)) at 1.
  unfold R.v26957, N.v26957.
  unfold R.v6, N.v6.
  rewrite ?node_26956.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26958 (s : N.State) (i : N.Inputs) :
  R.v26958 (state s) (inputs i) = Zmod.unsigned (N.v26958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26958 s i)) at 1.
  unfold R.v26958, N.v26958.
  rewrite ?node_10329.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26959 (s : N.State) (i : N.Inputs) :
  R.v26959 (state s) (inputs i) = Zmod.unsigned (N.v26959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26959 s i)) at 1.
  unfold R.v26959, N.v26959.
  unfold R.v6, N.v6.
  rewrite ?node_10486.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26960 (s : N.State) (i : N.Inputs) :
  R.v26960 (state s) (inputs i) = Zmod.unsigned (N.v26960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26960 s i)) at 1.
  unfold R.v26960, N.v26960.
  unfold R.v6, N.v6.
  rewrite ?node_10537.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26961 (s : N.State) (i : N.Inputs) :
  R.v26961 (state s) (inputs i) = Zmod.unsigned (N.v26961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26961 s i)) at 1.
  unfold R.v26961, N.v26961.
  rewrite ?node_26958.
  rewrite ?node_26959.
  rewrite ?node_26960.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26962 (s : N.State) (i : N.Inputs) :
  R.v26962 (state s) (inputs i) = Zmod.unsigned (N.v26962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26962 s i)) at 1.
  unfold R.v26962, N.v26962.
  rewrite ?node_26957.
  rewrite ?node_26961.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26963 (s : N.State) (i : N.Inputs) :
  R.v26963 (state s) (inputs i) = Zmod.unsigned (N.v26963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26963 s i)) at 1.
  unfold R.v26963, N.v26963.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26964 (s : N.State) (i : N.Inputs) :
  R.v26964 (state s) (inputs i) = Zmod.unsigned (N.v26964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26964 s i)) at 1.
  unfold R.v26964, N.v26964.
  unfold R.v16463, N.v16463.
  rewrite !state_r1142_nr_5F1142.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1142_nr_5F1142 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26965 (s : N.State) (i : N.Inputs) :
  R.v26965 (state s) (inputs i) = Zmod.unsigned (N.v26965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26965 s i)) at 1.
  unfold R.v26965, N.v26965.
  unfold R.v6, N.v6.
  rewrite !state_r1141_nr_5F1141.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1141_nr_5F1141 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26966 (s : N.State) (i : N.Inputs) :
  R.v26966 (state s) (inputs i) = Zmod.unsigned (N.v26966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26966 s i)) at 1.
  unfold R.v26966, N.v26966.
  unfold R.v6, N.v6.
  rewrite !state_r1140_nr_5F1140.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1140_nr_5F1140 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26967 (s : N.State) (i : N.Inputs) :
  R.v26967 (state s) (inputs i) = Zmod.unsigned (N.v26967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26967 s i)) at 1.
  unfold R.v26967, N.v26967.
  rewrite ?node_26965.
  rewrite ?node_26966.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26968 (s : N.State) (i : N.Inputs) :
  R.v26968 (state s) (inputs i) = Zmod.unsigned (N.v26968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26968 s i)) at 1.
  unfold R.v26968, N.v26968.
  unfold R.v16484, N.v16484.
  rewrite ?node_26967.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26969 (s : N.State) (i : N.Inputs) :
  R.v26969 (state s) (inputs i) = Zmod.unsigned (N.v26969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26969 s i)) at 1.
  unfold R.v26969, N.v26969.
  rewrite ?node_26964.
  rewrite ?node_26968.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26970 (s : N.State) (i : N.Inputs) :
  R.v26970 (state s) (inputs i) = Zmod.unsigned (N.v26970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26970 s i)) at 1.
  unfold R.v26970, N.v26970.
  unfold R.v6, N.v6.
  rewrite ?node_26969.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26971 (s : N.State) (i : N.Inputs) :
  R.v26971 (state s) (inputs i) = Zmod.unsigned (N.v26971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26971 s i)) at 1.
  unfold R.v26971, N.v26971.
  rewrite ?node_10324.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26972 (s : N.State) (i : N.Inputs) :
  R.v26972 (state s) (inputs i) = Zmod.unsigned (N.v26972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26972 s i)) at 1.
  unfold R.v26972, N.v26972.
  unfold R.v6, N.v6.
  rewrite ?node_10486.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26973 (s : N.State) (i : N.Inputs) :
  R.v26973 (state s) (inputs i) = Zmod.unsigned (N.v26973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26973 s i)) at 1.
  unfold R.v26973, N.v26973.
  rewrite ?node_26971.
  rewrite ?node_26972.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26974 (s : N.State) (i : N.Inputs) :
  R.v26974 (state s) (inputs i) = Zmod.unsigned (N.v26974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26974 s i)) at 1.
  unfold R.v26974, N.v26974.
  rewrite ?node_26970.
  rewrite ?node_26973.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26975 (s : N.State) (i : N.Inputs) :
  R.v26975 (state s) (inputs i) = Zmod.unsigned (N.v26975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26975 s i)) at 1.
  unfold R.v26975, N.v26975.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26976 (s : N.State) (i : N.Inputs) :
  R.v26976 (state s) (inputs i) = Zmod.unsigned (N.v26976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26976 s i)) at 1.
  unfold R.v26976, N.v26976.
  rewrite ?node_10328.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26977 (s : N.State) (i : N.Inputs) :
  R.v26977 (state s) (inputs i) = Zmod.unsigned (N.v26977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26977 s i)) at 1.
  unfold R.v26977, N.v26977.
  unfold R.v6, N.v6.
  rewrite !state_r1143_nr_5F1143.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1143_nr_5F1143 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26978 (s : N.State) (i : N.Inputs) :
  R.v26978 (state s) (inputs i) = Zmod.unsigned (N.v26978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26978 s i)) at 1.
  unfold R.v26978, N.v26978.
  unfold R.v6, N.v6.
  rewrite ?node_10324.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26979 (s : N.State) (i : N.Inputs) :
  R.v26979 (state s) (inputs i) = Zmod.unsigned (N.v26979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26979 s i)) at 1.
  unfold R.v26979, N.v26979.
  rewrite ?node_26977.
  rewrite ?node_26978.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26980 (s : N.State) (i : N.Inputs) :
  R.v26980 (state s) (inputs i) = Zmod.unsigned (N.v26980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26980 s i)) at 1.
  unfold R.v26980, N.v26980.
  unfold R.v16484, N.v16484.
  rewrite ?node_26979.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26981 (s : N.State) (i : N.Inputs) :
  R.v26981 (state s) (inputs i) = Zmod.unsigned (N.v26981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26981 s i)) at 1.
  unfold R.v26981, N.v26981.
  rewrite ?node_26976.
  rewrite ?node_26980.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26982 (s : N.State) (i : N.Inputs) :
  R.v26982 (state s) (inputs i) = Zmod.unsigned (N.v26982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26982 s i)) at 1.
  unfold R.v26982, N.v26982.
  unfold R.v6, N.v6.
  rewrite ?node_26981.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26983 (s : N.State) (i : N.Inputs) :
  R.v26983 (state s) (inputs i) = Zmod.unsigned (N.v26983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26983 s i)) at 1.
  unfold R.v26983, N.v26983.
  rewrite ?node_10329.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26984 (s : N.State) (i : N.Inputs) :
  R.v26984 (state s) (inputs i) = Zmod.unsigned (N.v26984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26984 s i)) at 1.
  unfold R.v26984, N.v26984.
  unfold R.v6, N.v6.
  rewrite ?node_10537.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26985 (s : N.State) (i : N.Inputs) :
  R.v26985 (state s) (inputs i) = Zmod.unsigned (N.v26985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26985 s i)) at 1.
  unfold R.v26985, N.v26985.
  rewrite ?node_26983.
  rewrite ?node_26984.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26986 (s : N.State) (i : N.Inputs) :
  R.v26986 (state s) (inputs i) = Zmod.unsigned (N.v26986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26986 s i)) at 1.
  unfold R.v26986, N.v26986.
  rewrite ?node_26982.
  rewrite ?node_26985.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26987 (s : N.State) (i : N.Inputs) :
  R.v26987 (state s) (inputs i) = Zmod.unsigned (N.v26987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26987 s i)) at 1.
  unfold R.v26987, N.v26987.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26988 (s : N.State) (i : N.Inputs) :
  R.v26988 (state s) (inputs i) = Zmod.unsigned (N.v26988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26988 s i)) at 1.
  unfold R.v26988, N.v26988.
  rewrite ?node_10336.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26989 (s : N.State) (i : N.Inputs) :
  R.v26989 (state s) (inputs i) = Zmod.unsigned (N.v26989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26989 s i)) at 1.
  unfold R.v26989, N.v26989.
  unfold R.v16463, N.v16463.
  rewrite !state_r1147_nr_5F1147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1147_nr_5F1147 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26990 (s : N.State) (i : N.Inputs) :
  R.v26990 (state s) (inputs i) = Zmod.unsigned (N.v26990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26990 s i)) at 1.
  unfold R.v26990, N.v26990.
  unfold R.v16463, N.v16463.
  rewrite !state_r1146_nr_5F1146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1146_nr_5F1146 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26991 (s : N.State) (i : N.Inputs) :
  R.v26991 (state s) (inputs i) = Zmod.unsigned (N.v26991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26991 s i)) at 1.
  unfold R.v26991, N.v26991.
  unfold R.v6, N.v6.
  rewrite !state_r1145_nr_5F1145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1145_nr_5F1145 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26992 (s : N.State) (i : N.Inputs) :
  R.v26992 (state s) (inputs i) = Zmod.unsigned (N.v26992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26992 s i)) at 1.
  unfold R.v26992, N.v26992.
  unfold R.v6, N.v6.
  rewrite !state_r1144_nr_5F1144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r1144_nr_5F1144 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26993 (s : N.State) (i : N.Inputs) :
  R.v26993 (state s) (inputs i) = Zmod.unsigned (N.v26993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26993 s i)) at 1.
  unfold R.v26993, N.v26993.
  rewrite ?node_26991.
  rewrite ?node_26992.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26994 (s : N.State) (i : N.Inputs) :
  R.v26994 (state s) (inputs i) = Zmod.unsigned (N.v26994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26994 s i)) at 1.
  unfold R.v26994, N.v26994.
  unfold R.v16484, N.v16484.
  rewrite ?node_26993.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26995 (s : N.State) (i : N.Inputs) :
  R.v26995 (state s) (inputs i) = Zmod.unsigned (N.v26995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26995 s i)) at 1.
  unfold R.v26995, N.v26995.
  rewrite ?node_26988.
  rewrite ?node_26989.
  rewrite ?node_26990.
  rewrite ?node_26994.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26996 (s : N.State) (i : N.Inputs) :
  R.v26996 (state s) (inputs i) = Zmod.unsigned (N.v26996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26996 s i)) at 1.
  unfold R.v26996, N.v26996.
  unfold R.v6, N.v6.
  rewrite ?node_26995.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26997 (s : N.State) (i : N.Inputs) :
  R.v26997 (state s) (inputs i) = Zmod.unsigned (N.v26997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26997 s i)) at 1.
  unfold R.v26997, N.v26997.
  rewrite ?node_10337.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26998 (s : N.State) (i : N.Inputs) :
  R.v26998 (state s) (inputs i) = Zmod.unsigned (N.v26998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26998 s i)) at 1.
  unfold R.v26998, N.v26998.
  unfold R.v6, N.v6.
  rewrite ?node_10494.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_26999 (s : N.State) (i : N.Inputs) :
  R.v26999 (state s) (inputs i) = Zmod.unsigned (N.v26999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v26999 s i)) at 1.
  unfold R.v26999, N.v26999.
  unfold R.v6, N.v6.
  rewrite ?node_10541.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
