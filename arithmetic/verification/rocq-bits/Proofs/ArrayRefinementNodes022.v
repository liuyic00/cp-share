(* Generated node equalities; not yet a whole-circuit refinement. *)
    From Stdlib Require Import ZArith Lia Zmod.Bits.
    From BitsProofs Require Export ArrayRefinementBase.
    From BitsProofs Require Import RefinementTactics.
    Open Scope Z_scope.

From BitsProofs Require Export ArrayRefinementNodes021.
Lemma node_22000 (s : N.State) (i : N.Inputs) :
  R.v22000 (state s) (inputs i) = Zmod.unsigned (N.v22000 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22000 s i)) at 1.
  unfold R.v22000, N.v22000.
  unfold R.v16463, N.v16463.
  rewrite !state_r616_nr_5F616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r616_nr_5F616 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22001 (s : N.State) (i : N.Inputs) :
  R.v22001 (state s) (inputs i) = Zmod.unsigned (N.v22001 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22001 s i)) at 1.
  unfold R.v22001, N.v22001.
  unfold R.v6, N.v6.
  rewrite !state_r615_nr_5F615.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r615_nr_5F615 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22002 (s : N.State) (i : N.Inputs) :
  R.v22002 (state s) (inputs i) = Zmod.unsigned (N.v22002 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22002 s i)) at 1.
  unfold R.v22002, N.v22002.
  unfold R.v6, N.v6.
  rewrite !state_r614_nr_5F614.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r614_nr_5F614 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22003 (s : N.State) (i : N.Inputs) :
  R.v22003 (state s) (inputs i) = Zmod.unsigned (N.v22003 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22003 s i)) at 1.
  unfold R.v22003, N.v22003.
  rewrite ?node_22001.
  rewrite ?node_22002.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22004 (s : N.State) (i : N.Inputs) :
  R.v22004 (state s) (inputs i) = Zmod.unsigned (N.v22004 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22004 s i)) at 1.
  unfold R.v22004, N.v22004.
  unfold R.v16484, N.v16484.
  rewrite ?node_22003.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22005 (s : N.State) (i : N.Inputs) :
  R.v22005 (state s) (inputs i) = Zmod.unsigned (N.v22005 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22005 s i)) at 1.
  unfold R.v22005, N.v22005.
  rewrite ?node_21998.
  rewrite ?node_21999.
  rewrite ?node_22000.
  rewrite ?node_22004.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22006 (s : N.State) (i : N.Inputs) :
  R.v22006 (state s) (inputs i) = Zmod.unsigned (N.v22006 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22006 s i)) at 1.
  unfold R.v22006, N.v22006.
  unfold R.v6, N.v6.
  rewrite ?node_22005.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22007 (s : N.State) (i : N.Inputs) :
  R.v22007 (state s) (inputs i) = Zmod.unsigned (N.v22007 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22007 s i)) at 1.
  unfold R.v22007, N.v22007.
  rewrite ?node_7858.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22008 (s : N.State) (i : N.Inputs) :
  R.v22008 (state s) (inputs i) = Zmod.unsigned (N.v22008 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22008 s i)) at 1.
  unfold R.v22008, N.v22008.
  unfold R.v6, N.v6.
  rewrite ?node_7974.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22009 (s : N.State) (i : N.Inputs) :
  R.v22009 (state s) (inputs i) = Zmod.unsigned (N.v22009 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22009 s i)) at 1.
  unfold R.v22009, N.v22009.
  unfold R.v6, N.v6.
  rewrite ?node_8007.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22010 (s : N.State) (i : N.Inputs) :
  R.v22010 (state s) (inputs i) = Zmod.unsigned (N.v22010 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22010 s i)) at 1.
  unfold R.v22010, N.v22010.
  rewrite ?node_22007.
  rewrite ?node_22008.
  rewrite ?node_22009.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22011 (s : N.State) (i : N.Inputs) :
  R.v22011 (state s) (inputs i) = Zmod.unsigned (N.v22011 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22011 s i)) at 1.
  unfold R.v22011, N.v22011.
  rewrite ?node_22006.
  rewrite ?node_22010.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22012 (s : N.State) (i : N.Inputs) :
  R.v22012 (state s) (inputs i) = Zmod.unsigned (N.v22012 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22012 s i)) at 1.
  unfold R.v22012, N.v22012.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22013 (s : N.State) (i : N.Inputs) :
  R.v22013 (state s) (inputs i) = Zmod.unsigned (N.v22013 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22013 s i)) at 1.
  unfold R.v22013, N.v22013.
  unfold R.v16463, N.v16463.
  rewrite !state_r616_nr_5F616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r616_nr_5F616 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22014 (s : N.State) (i : N.Inputs) :
  R.v22014 (state s) (inputs i) = Zmod.unsigned (N.v22014 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22014 s i)) at 1.
  unfold R.v22014, N.v22014.
  unfold R.v6, N.v6.
  rewrite !state_r615_nr_5F615.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r615_nr_5F615 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22015 (s : N.State) (i : N.Inputs) :
  R.v22015 (state s) (inputs i) = Zmod.unsigned (N.v22015 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22015 s i)) at 1.
  unfold R.v22015, N.v22015.
  unfold R.v6, N.v6.
  rewrite !state_r614_nr_5F614.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r614_nr_5F614 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22016 (s : N.State) (i : N.Inputs) :
  R.v22016 (state s) (inputs i) = Zmod.unsigned (N.v22016 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22016 s i)) at 1.
  unfold R.v22016, N.v22016.
  rewrite ?node_22014.
  rewrite ?node_22015.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22017 (s : N.State) (i : N.Inputs) :
  R.v22017 (state s) (inputs i) = Zmod.unsigned (N.v22017 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22017 s i)) at 1.
  unfold R.v22017, N.v22017.
  unfold R.v16484, N.v16484.
  rewrite ?node_22016.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22018 (s : N.State) (i : N.Inputs) :
  R.v22018 (state s) (inputs i) = Zmod.unsigned (N.v22018 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22018 s i)) at 1.
  unfold R.v22018, N.v22018.
  rewrite ?node_22013.
  rewrite ?node_22017.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22019 (s : N.State) (i : N.Inputs) :
  R.v22019 (state s) (inputs i) = Zmod.unsigned (N.v22019 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22019 s i)) at 1.
  unfold R.v22019, N.v22019.
  unfold R.v6, N.v6.
  rewrite ?node_22018.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22020 (s : N.State) (i : N.Inputs) :
  R.v22020 (state s) (inputs i) = Zmod.unsigned (N.v22020 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22020 s i)) at 1.
  unfold R.v22020, N.v22020.
  rewrite ?node_7853.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22021 (s : N.State) (i : N.Inputs) :
  R.v22021 (state s) (inputs i) = Zmod.unsigned (N.v22021 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22021 s i)) at 1.
  unfold R.v22021, N.v22021.
  unfold R.v6, N.v6.
  rewrite ?node_7974.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22022 (s : N.State) (i : N.Inputs) :
  R.v22022 (state s) (inputs i) = Zmod.unsigned (N.v22022 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22022 s i)) at 1.
  unfold R.v22022, N.v22022.
  rewrite ?node_22020.
  rewrite ?node_22021.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22023 (s : N.State) (i : N.Inputs) :
  R.v22023 (state s) (inputs i) = Zmod.unsigned (N.v22023 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22023 s i)) at 1.
  unfold R.v22023, N.v22023.
  rewrite ?node_22019.
  rewrite ?node_22022.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22024 (s : N.State) (i : N.Inputs) :
  R.v22024 (state s) (inputs i) = Zmod.unsigned (N.v22024 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22024 s i)) at 1.
  unfold R.v22024, N.v22024.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22025 (s : N.State) (i : N.Inputs) :
  R.v22025 (state s) (inputs i) = Zmod.unsigned (N.v22025 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22025 s i)) at 1.
  unfold R.v22025, N.v22025.
  rewrite ?node_7857.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22026 (s : N.State) (i : N.Inputs) :
  R.v22026 (state s) (inputs i) = Zmod.unsigned (N.v22026 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22026 s i)) at 1.
  unfold R.v22026, N.v22026.
  unfold R.v6, N.v6.
  rewrite !state_r617_nr_5F617.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r617_nr_5F617 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22027 (s : N.State) (i : N.Inputs) :
  R.v22027 (state s) (inputs i) = Zmod.unsigned (N.v22027 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22027 s i)) at 1.
  unfold R.v22027, N.v22027.
  unfold R.v6, N.v6.
  rewrite ?node_7853.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22028 (s : N.State) (i : N.Inputs) :
  R.v22028 (state s) (inputs i) = Zmod.unsigned (N.v22028 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22028 s i)) at 1.
  unfold R.v22028, N.v22028.
  rewrite ?node_22026.
  rewrite ?node_22027.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22029 (s : N.State) (i : N.Inputs) :
  R.v22029 (state s) (inputs i) = Zmod.unsigned (N.v22029 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22029 s i)) at 1.
  unfold R.v22029, N.v22029.
  unfold R.v16484, N.v16484.
  rewrite ?node_22028.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22030 (s : N.State) (i : N.Inputs) :
  R.v22030 (state s) (inputs i) = Zmod.unsigned (N.v22030 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22030 s i)) at 1.
  unfold R.v22030, N.v22030.
  rewrite ?node_22025.
  rewrite ?node_22029.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22031 (s : N.State) (i : N.Inputs) :
  R.v22031 (state s) (inputs i) = Zmod.unsigned (N.v22031 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22031 s i)) at 1.
  unfold R.v22031, N.v22031.
  unfold R.v6, N.v6.
  rewrite ?node_22030.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22032 (s : N.State) (i : N.Inputs) :
  R.v22032 (state s) (inputs i) = Zmod.unsigned (N.v22032 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22032 s i)) at 1.
  unfold R.v22032, N.v22032.
  rewrite ?node_7858.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22033 (s : N.State) (i : N.Inputs) :
  R.v22033 (state s) (inputs i) = Zmod.unsigned (N.v22033 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22033 s i)) at 1.
  unfold R.v22033, N.v22033.
  unfold R.v6, N.v6.
  rewrite ?node_8007.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22034 (s : N.State) (i : N.Inputs) :
  R.v22034 (state s) (inputs i) = Zmod.unsigned (N.v22034 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22034 s i)) at 1.
  unfold R.v22034, N.v22034.
  rewrite ?node_22032.
  rewrite ?node_22033.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22035 (s : N.State) (i : N.Inputs) :
  R.v22035 (state s) (inputs i) = Zmod.unsigned (N.v22035 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22035 s i)) at 1.
  unfold R.v22035, N.v22035.
  rewrite ?node_22031.
  rewrite ?node_22034.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22036 (s : N.State) (i : N.Inputs) :
  R.v22036 (state s) (inputs i) = Zmod.unsigned (N.v22036 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22036 s i)) at 1.
  unfold R.v22036, N.v22036.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22037 (s : N.State) (i : N.Inputs) :
  R.v22037 (state s) (inputs i) = Zmod.unsigned (N.v22037 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22037 s i)) at 1.
  unfold R.v22037, N.v22037.
  rewrite ?node_7864.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22038 (s : N.State) (i : N.Inputs) :
  R.v22038 (state s) (inputs i) = Zmod.unsigned (N.v22038 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22038 s i)) at 1.
  unfold R.v22038, N.v22038.
  unfold R.v16463, N.v16463.
  rewrite !state_r621_nr_5F621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r621_nr_5F621 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22039 (s : N.State) (i : N.Inputs) :
  R.v22039 (state s) (inputs i) = Zmod.unsigned (N.v22039 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22039 s i)) at 1.
  unfold R.v22039, N.v22039.
  unfold R.v16463, N.v16463.
  rewrite !state_r620_nr_5F620.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r620_nr_5F620 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22040 (s : N.State) (i : N.Inputs) :
  R.v22040 (state s) (inputs i) = Zmod.unsigned (N.v22040 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22040 s i)) at 1.
  unfold R.v22040, N.v22040.
  unfold R.v6, N.v6.
  rewrite !state_r619_nr_5F619.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r619_nr_5F619 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22041 (s : N.State) (i : N.Inputs) :
  R.v22041 (state s) (inputs i) = Zmod.unsigned (N.v22041 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22041 s i)) at 1.
  unfold R.v22041, N.v22041.
  unfold R.v6, N.v6.
  rewrite !state_r618_nr_5F618.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r618_nr_5F618 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22042 (s : N.State) (i : N.Inputs) :
  R.v22042 (state s) (inputs i) = Zmod.unsigned (N.v22042 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22042 s i)) at 1.
  unfold R.v22042, N.v22042.
  rewrite ?node_22040.
  rewrite ?node_22041.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22043 (s : N.State) (i : N.Inputs) :
  R.v22043 (state s) (inputs i) = Zmod.unsigned (N.v22043 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22043 s i)) at 1.
  unfold R.v22043, N.v22043.
  unfold R.v16484, N.v16484.
  rewrite ?node_22042.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22044 (s : N.State) (i : N.Inputs) :
  R.v22044 (state s) (inputs i) = Zmod.unsigned (N.v22044 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22044 s i)) at 1.
  unfold R.v22044, N.v22044.
  rewrite ?node_22037.
  rewrite ?node_22038.
  rewrite ?node_22039.
  rewrite ?node_22043.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22045 (s : N.State) (i : N.Inputs) :
  R.v22045 (state s) (inputs i) = Zmod.unsigned (N.v22045 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22045 s i)) at 1.
  unfold R.v22045, N.v22045.
  unfold R.v6, N.v6.
  rewrite ?node_22044.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22046 (s : N.State) (i : N.Inputs) :
  R.v22046 (state s) (inputs i) = Zmod.unsigned (N.v22046 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22046 s i)) at 1.
  unfold R.v22046, N.v22046.
  rewrite ?node_7865.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22047 (s : N.State) (i : N.Inputs) :
  R.v22047 (state s) (inputs i) = Zmod.unsigned (N.v22047 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22047 s i)) at 1.
  unfold R.v22047, N.v22047.
  unfold R.v6, N.v6.
  rewrite ?node_7981.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22048 (s : N.State) (i : N.Inputs) :
  R.v22048 (state s) (inputs i) = Zmod.unsigned (N.v22048 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22048 s i)) at 1.
  unfold R.v22048, N.v22048.
  unfold R.v6, N.v6.
  rewrite ?node_8016.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22049 (s : N.State) (i : N.Inputs) :
  R.v22049 (state s) (inputs i) = Zmod.unsigned (N.v22049 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22049 s i)) at 1.
  unfold R.v22049, N.v22049.
  rewrite ?node_22046.
  rewrite ?node_22047.
  rewrite ?node_22048.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22050 (s : N.State) (i : N.Inputs) :
  R.v22050 (state s) (inputs i) = Zmod.unsigned (N.v22050 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22050 s i)) at 1.
  unfold R.v22050, N.v22050.
  rewrite ?node_22045.
  rewrite ?node_22049.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22051 (s : N.State) (i : N.Inputs) :
  R.v22051 (state s) (inputs i) = Zmod.unsigned (N.v22051 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22051 s i)) at 1.
  unfold R.v22051, N.v22051.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22052 (s : N.State) (i : N.Inputs) :
  R.v22052 (state s) (inputs i) = Zmod.unsigned (N.v22052 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22052 s i)) at 1.
  unfold R.v22052, N.v22052.
  unfold R.v16463, N.v16463.
  rewrite !state_r620_nr_5F620.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r620_nr_5F620 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22053 (s : N.State) (i : N.Inputs) :
  R.v22053 (state s) (inputs i) = Zmod.unsigned (N.v22053 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22053 s i)) at 1.
  unfold R.v22053, N.v22053.
  unfold R.v6, N.v6.
  rewrite !state_r619_nr_5F619.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r619_nr_5F619 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22054 (s : N.State) (i : N.Inputs) :
  R.v22054 (state s) (inputs i) = Zmod.unsigned (N.v22054 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22054 s i)) at 1.
  unfold R.v22054, N.v22054.
  unfold R.v6, N.v6.
  rewrite !state_r618_nr_5F618.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r618_nr_5F618 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22055 (s : N.State) (i : N.Inputs) :
  R.v22055 (state s) (inputs i) = Zmod.unsigned (N.v22055 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22055 s i)) at 1.
  unfold R.v22055, N.v22055.
  rewrite ?node_22053.
  rewrite ?node_22054.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22056 (s : N.State) (i : N.Inputs) :
  R.v22056 (state s) (inputs i) = Zmod.unsigned (N.v22056 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22056 s i)) at 1.
  unfold R.v22056, N.v22056.
  unfold R.v16484, N.v16484.
  rewrite ?node_22055.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22057 (s : N.State) (i : N.Inputs) :
  R.v22057 (state s) (inputs i) = Zmod.unsigned (N.v22057 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22057 s i)) at 1.
  unfold R.v22057, N.v22057.
  rewrite ?node_22052.
  rewrite ?node_22056.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22058 (s : N.State) (i : N.Inputs) :
  R.v22058 (state s) (inputs i) = Zmod.unsigned (N.v22058 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22058 s i)) at 1.
  unfold R.v22058, N.v22058.
  unfold R.v6, N.v6.
  rewrite ?node_22057.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22059 (s : N.State) (i : N.Inputs) :
  R.v22059 (state s) (inputs i) = Zmod.unsigned (N.v22059 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22059 s i)) at 1.
  unfold R.v22059, N.v22059.
  rewrite ?node_7860.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22060 (s : N.State) (i : N.Inputs) :
  R.v22060 (state s) (inputs i) = Zmod.unsigned (N.v22060 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22060 s i)) at 1.
  unfold R.v22060, N.v22060.
  unfold R.v6, N.v6.
  rewrite ?node_7981.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22061 (s : N.State) (i : N.Inputs) :
  R.v22061 (state s) (inputs i) = Zmod.unsigned (N.v22061 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22061 s i)) at 1.
  unfold R.v22061, N.v22061.
  rewrite ?node_22059.
  rewrite ?node_22060.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22062 (s : N.State) (i : N.Inputs) :
  R.v22062 (state s) (inputs i) = Zmod.unsigned (N.v22062 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22062 s i)) at 1.
  unfold R.v22062, N.v22062.
  rewrite ?node_22058.
  rewrite ?node_22061.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22063 (s : N.State) (i : N.Inputs) :
  R.v22063 (state s) (inputs i) = Zmod.unsigned (N.v22063 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22063 s i)) at 1.
  unfold R.v22063, N.v22063.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22064 (s : N.State) (i : N.Inputs) :
  R.v22064 (state s) (inputs i) = Zmod.unsigned (N.v22064 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22064 s i)) at 1.
  unfold R.v22064, N.v22064.
  rewrite ?node_7864.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22065 (s : N.State) (i : N.Inputs) :
  R.v22065 (state s) (inputs i) = Zmod.unsigned (N.v22065 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22065 s i)) at 1.
  unfold R.v22065, N.v22065.
  unfold R.v6, N.v6.
  rewrite !state_r621_nr_5F621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r621_nr_5F621 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22066 (s : N.State) (i : N.Inputs) :
  R.v22066 (state s) (inputs i) = Zmod.unsigned (N.v22066 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22066 s i)) at 1.
  unfold R.v22066, N.v22066.
  unfold R.v6, N.v6.
  rewrite ?node_7860.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22067 (s : N.State) (i : N.Inputs) :
  R.v22067 (state s) (inputs i) = Zmod.unsigned (N.v22067 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22067 s i)) at 1.
  unfold R.v22067, N.v22067.
  rewrite ?node_22065.
  rewrite ?node_22066.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22068 (s : N.State) (i : N.Inputs) :
  R.v22068 (state s) (inputs i) = Zmod.unsigned (N.v22068 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22068 s i)) at 1.
  unfold R.v22068, N.v22068.
  unfold R.v16484, N.v16484.
  rewrite ?node_22067.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22069 (s : N.State) (i : N.Inputs) :
  R.v22069 (state s) (inputs i) = Zmod.unsigned (N.v22069 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22069 s i)) at 1.
  unfold R.v22069, N.v22069.
  rewrite ?node_22064.
  rewrite ?node_22068.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22070 (s : N.State) (i : N.Inputs) :
  R.v22070 (state s) (inputs i) = Zmod.unsigned (N.v22070 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22070 s i)) at 1.
  unfold R.v22070, N.v22070.
  unfold R.v6, N.v6.
  rewrite ?node_22069.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22071 (s : N.State) (i : N.Inputs) :
  R.v22071 (state s) (inputs i) = Zmod.unsigned (N.v22071 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22071 s i)) at 1.
  unfold R.v22071, N.v22071.
  rewrite ?node_7865.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22072 (s : N.State) (i : N.Inputs) :
  R.v22072 (state s) (inputs i) = Zmod.unsigned (N.v22072 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22072 s i)) at 1.
  unfold R.v22072, N.v22072.
  unfold R.v6, N.v6.
  rewrite ?node_8016.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22073 (s : N.State) (i : N.Inputs) :
  R.v22073 (state s) (inputs i) = Zmod.unsigned (N.v22073 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22073 s i)) at 1.
  unfold R.v22073, N.v22073.
  rewrite ?node_22071.
  rewrite ?node_22072.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22074 (s : N.State) (i : N.Inputs) :
  R.v22074 (state s) (inputs i) = Zmod.unsigned (N.v22074 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22074 s i)) at 1.
  unfold R.v22074, N.v22074.
  rewrite ?node_22070.
  rewrite ?node_22073.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22075 (s : N.State) (i : N.Inputs) :
  R.v22075 (state s) (inputs i) = Zmod.unsigned (N.v22075 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22075 s i)) at 1.
  unfold R.v22075, N.v22075.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22076 (s : N.State) (i : N.Inputs) :
  R.v22076 (state s) (inputs i) = Zmod.unsigned (N.v22076 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22076 s i)) at 1.
  unfold R.v22076, N.v22076.
  rewrite ?node_7939.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22077 (s : N.State) (i : N.Inputs) :
  R.v22077 (state s) (inputs i) = Zmod.unsigned (N.v22077 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22077 s i)) at 1.
  unfold R.v22077, N.v22077.
  unfold R.v16463, N.v16463.
  rewrite !state_r626_nr_5F626.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r626_nr_5F626 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22078 (s : N.State) (i : N.Inputs) :
  R.v22078 (state s) (inputs i) = Zmod.unsigned (N.v22078 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22078 s i)) at 1.
  unfold R.v22078, N.v22078.
  unfold R.v16463, N.v16463.
  rewrite !state_r625_nr_5F625.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r625_nr_5F625 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22079 (s : N.State) (i : N.Inputs) :
  R.v22079 (state s) (inputs i) = Zmod.unsigned (N.v22079 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22079 s i)) at 1.
  unfold R.v22079, N.v22079.
  unfold R.v6, N.v6.
  rewrite !state_r624_nr_5F624.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r624_nr_5F624 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22080 (s : N.State) (i : N.Inputs) :
  R.v22080 (state s) (inputs i) = Zmod.unsigned (N.v22080 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22080 s i)) at 1.
  unfold R.v22080, N.v22080.
  unfold R.v6, N.v6.
  rewrite !state_r623_nr_5F623.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r623_nr_5F623 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22081 (s : N.State) (i : N.Inputs) :
  R.v22081 (state s) (inputs i) = Zmod.unsigned (N.v22081 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22081 s i)) at 1.
  unfold R.v22081, N.v22081.
  rewrite ?node_22079.
  rewrite ?node_22080.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22082 (s : N.State) (i : N.Inputs) :
  R.v22082 (state s) (inputs i) = Zmod.unsigned (N.v22082 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22082 s i)) at 1.
  unfold R.v22082, N.v22082.
  unfold R.v16484, N.v16484.
  rewrite ?node_22081.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22083 (s : N.State) (i : N.Inputs) :
  R.v22083 (state s) (inputs i) = Zmod.unsigned (N.v22083 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22083 s i)) at 1.
  unfold R.v22083, N.v22083.
  rewrite ?node_22076.
  rewrite ?node_22077.
  rewrite ?node_22078.
  rewrite ?node_22082.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22084 (s : N.State) (i : N.Inputs) :
  R.v22084 (state s) (inputs i) = Zmod.unsigned (N.v22084 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22084 s i)) at 1.
  unfold R.v22084, N.v22084.
  unfold R.v6, N.v6.
  rewrite ?node_22083.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22085 (s : N.State) (i : N.Inputs) :
  R.v22085 (state s) (inputs i) = Zmod.unsigned (N.v22085 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22085 s i)) at 1.
  unfold R.v22085, N.v22085.
  rewrite ?node_7940.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22086 (s : N.State) (i : N.Inputs) :
  R.v22086 (state s) (inputs i) = Zmod.unsigned (N.v22086 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22086 s i)) at 1.
  unfold R.v22086, N.v22086.
  unfold R.v6, N.v6.
  rewrite ?node_8058.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22087 (s : N.State) (i : N.Inputs) :
  R.v22087 (state s) (inputs i) = Zmod.unsigned (N.v22087 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22087 s i)) at 1.
  unfold R.v22087, N.v22087.
  unfold R.v6, N.v6.
  rewrite ?node_8107.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22088 (s : N.State) (i : N.Inputs) :
  R.v22088 (state s) (inputs i) = Zmod.unsigned (N.v22088 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22088 s i)) at 1.
  unfold R.v22088, N.v22088.
  rewrite ?node_22085.
  rewrite ?node_22086.
  rewrite ?node_22087.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22089 (s : N.State) (i : N.Inputs) :
  R.v22089 (state s) (inputs i) = Zmod.unsigned (N.v22089 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22089 s i)) at 1.
  unfold R.v22089, N.v22089.
  rewrite ?node_22084.
  rewrite ?node_22088.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22090 (s : N.State) (i : N.Inputs) :
  R.v22090 (state s) (inputs i) = Zmod.unsigned (N.v22090 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22090 s i)) at 1.
  unfold R.v22090, N.v22090.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22091 (s : N.State) (i : N.Inputs) :
  R.v22091 (state s) (inputs i) = Zmod.unsigned (N.v22091 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22091 s i)) at 1.
  unfold R.v22091, N.v22091.
  unfold R.v16463, N.v16463.
  rewrite !state_r625_nr_5F625.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r625_nr_5F625 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22092 (s : N.State) (i : N.Inputs) :
  R.v22092 (state s) (inputs i) = Zmod.unsigned (N.v22092 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22092 s i)) at 1.
  unfold R.v22092, N.v22092.
  unfold R.v6, N.v6.
  rewrite !state_r624_nr_5F624.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r624_nr_5F624 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22093 (s : N.State) (i : N.Inputs) :
  R.v22093 (state s) (inputs i) = Zmod.unsigned (N.v22093 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22093 s i)) at 1.
  unfold R.v22093, N.v22093.
  unfold R.v6, N.v6.
  rewrite !state_r623_nr_5F623.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r623_nr_5F623 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22094 (s : N.State) (i : N.Inputs) :
  R.v22094 (state s) (inputs i) = Zmod.unsigned (N.v22094 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22094 s i)) at 1.
  unfold R.v22094, N.v22094.
  rewrite ?node_22092.
  rewrite ?node_22093.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22095 (s : N.State) (i : N.Inputs) :
  R.v22095 (state s) (inputs i) = Zmod.unsigned (N.v22095 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22095 s i)) at 1.
  unfold R.v22095, N.v22095.
  unfold R.v16484, N.v16484.
  rewrite ?node_22094.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22096 (s : N.State) (i : N.Inputs) :
  R.v22096 (state s) (inputs i) = Zmod.unsigned (N.v22096 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22096 s i)) at 1.
  unfold R.v22096, N.v22096.
  rewrite ?node_22091.
  rewrite ?node_22095.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22097 (s : N.State) (i : N.Inputs) :
  R.v22097 (state s) (inputs i) = Zmod.unsigned (N.v22097 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22097 s i)) at 1.
  unfold R.v22097, N.v22097.
  unfold R.v6, N.v6.
  rewrite ?node_22096.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22098 (s : N.State) (i : N.Inputs) :
  R.v22098 (state s) (inputs i) = Zmod.unsigned (N.v22098 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22098 s i)) at 1.
  unfold R.v22098, N.v22098.
  rewrite ?node_7935.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22099 (s : N.State) (i : N.Inputs) :
  R.v22099 (state s) (inputs i) = Zmod.unsigned (N.v22099 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22099 s i)) at 1.
  unfold R.v22099, N.v22099.
  unfold R.v6, N.v6.
  rewrite ?node_8058.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22100 (s : N.State) (i : N.Inputs) :
  R.v22100 (state s) (inputs i) = Zmod.unsigned (N.v22100 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22100 s i)) at 1.
  unfold R.v22100, N.v22100.
  rewrite ?node_22098.
  rewrite ?node_22099.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22101 (s : N.State) (i : N.Inputs) :
  R.v22101 (state s) (inputs i) = Zmod.unsigned (N.v22101 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22101 s i)) at 1.
  unfold R.v22101, N.v22101.
  rewrite ?node_22097.
  rewrite ?node_22100.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22102 (s : N.State) (i : N.Inputs) :
  R.v22102 (state s) (inputs i) = Zmod.unsigned (N.v22102 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22102 s i)) at 1.
  unfold R.v22102, N.v22102.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22103 (s : N.State) (i : N.Inputs) :
  R.v22103 (state s) (inputs i) = Zmod.unsigned (N.v22103 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22103 s i)) at 1.
  unfold R.v22103, N.v22103.
  rewrite ?node_7939.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22104 (s : N.State) (i : N.Inputs) :
  R.v22104 (state s) (inputs i) = Zmod.unsigned (N.v22104 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22104 s i)) at 1.
  unfold R.v22104, N.v22104.
  unfold R.v6, N.v6.
  rewrite !state_r626_nr_5F626.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r626_nr_5F626 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22105 (s : N.State) (i : N.Inputs) :
  R.v22105 (state s) (inputs i) = Zmod.unsigned (N.v22105 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22105 s i)) at 1.
  unfold R.v22105, N.v22105.
  unfold R.v6, N.v6.
  rewrite ?node_7935.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22106 (s : N.State) (i : N.Inputs) :
  R.v22106 (state s) (inputs i) = Zmod.unsigned (N.v22106 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22106 s i)) at 1.
  unfold R.v22106, N.v22106.
  rewrite ?node_22104.
  rewrite ?node_22105.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22107 (s : N.State) (i : N.Inputs) :
  R.v22107 (state s) (inputs i) = Zmod.unsigned (N.v22107 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22107 s i)) at 1.
  unfold R.v22107, N.v22107.
  unfold R.v16484, N.v16484.
  rewrite ?node_22106.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22108 (s : N.State) (i : N.Inputs) :
  R.v22108 (state s) (inputs i) = Zmod.unsigned (N.v22108 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22108 s i)) at 1.
  unfold R.v22108, N.v22108.
  rewrite ?node_22103.
  rewrite ?node_22107.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22109 (s : N.State) (i : N.Inputs) :
  R.v22109 (state s) (inputs i) = Zmod.unsigned (N.v22109 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22109 s i)) at 1.
  unfold R.v22109, N.v22109.
  unfold R.v6, N.v6.
  rewrite ?node_22108.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22110 (s : N.State) (i : N.Inputs) :
  R.v22110 (state s) (inputs i) = Zmod.unsigned (N.v22110 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22110 s i)) at 1.
  unfold R.v22110, N.v22110.
  rewrite ?node_7940.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22111 (s : N.State) (i : N.Inputs) :
  R.v22111 (state s) (inputs i) = Zmod.unsigned (N.v22111 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22111 s i)) at 1.
  unfold R.v22111, N.v22111.
  unfold R.v6, N.v6.
  rewrite ?node_8107.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22112 (s : N.State) (i : N.Inputs) :
  R.v22112 (state s) (inputs i) = Zmod.unsigned (N.v22112 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22112 s i)) at 1.
  unfold R.v22112, N.v22112.
  rewrite ?node_22110.
  rewrite ?node_22111.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22113 (s : N.State) (i : N.Inputs) :
  R.v22113 (state s) (inputs i) = Zmod.unsigned (N.v22113 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22113 s i)) at 1.
  unfold R.v22113, N.v22113.
  rewrite ?node_22109.
  rewrite ?node_22112.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22114 (s : N.State) (i : N.Inputs) :
  R.v22114 (state s) (inputs i) = Zmod.unsigned (N.v22114 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22114 s i)) at 1.
  unfold R.v22114, N.v22114.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22115 (s : N.State) (i : N.Inputs) :
  R.v22115 (state s) (inputs i) = Zmod.unsigned (N.v22115 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22115 s i)) at 1.
  unfold R.v22115, N.v22115.
  rewrite ?node_7946.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22116 (s : N.State) (i : N.Inputs) :
  R.v22116 (state s) (inputs i) = Zmod.unsigned (N.v22116 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22116 s i)) at 1.
  unfold R.v22116, N.v22116.
  unfold R.v16463, N.v16463.
  rewrite !state_r630_nr_5F630.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r630_nr_5F630 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22117 (s : N.State) (i : N.Inputs) :
  R.v22117 (state s) (inputs i) = Zmod.unsigned (N.v22117 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22117 s i)) at 1.
  unfold R.v22117, N.v22117.
  unfold R.v16463, N.v16463.
  rewrite !state_r629_nr_5F629.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r629_nr_5F629 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22118 (s : N.State) (i : N.Inputs) :
  R.v22118 (state s) (inputs i) = Zmod.unsigned (N.v22118 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22118 s i)) at 1.
  unfold R.v22118, N.v22118.
  unfold R.v6, N.v6.
  rewrite !state_r628_nr_5F628.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r628_nr_5F628 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22119 (s : N.State) (i : N.Inputs) :
  R.v22119 (state s) (inputs i) = Zmod.unsigned (N.v22119 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22119 s i)) at 1.
  unfold R.v22119, N.v22119.
  unfold R.v6, N.v6.
  rewrite !state_r627_nr_5F627.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r627_nr_5F627 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22120 (s : N.State) (i : N.Inputs) :
  R.v22120 (state s) (inputs i) = Zmod.unsigned (N.v22120 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22120 s i)) at 1.
  unfold R.v22120, N.v22120.
  rewrite ?node_22118.
  rewrite ?node_22119.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22121 (s : N.State) (i : N.Inputs) :
  R.v22121 (state s) (inputs i) = Zmod.unsigned (N.v22121 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22121 s i)) at 1.
  unfold R.v22121, N.v22121.
  unfold R.v16484, N.v16484.
  rewrite ?node_22120.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22122 (s : N.State) (i : N.Inputs) :
  R.v22122 (state s) (inputs i) = Zmod.unsigned (N.v22122 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22122 s i)) at 1.
  unfold R.v22122, N.v22122.
  rewrite ?node_22115.
  rewrite ?node_22116.
  rewrite ?node_22117.
  rewrite ?node_22121.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22123 (s : N.State) (i : N.Inputs) :
  R.v22123 (state s) (inputs i) = Zmod.unsigned (N.v22123 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22123 s i)) at 1.
  unfold R.v22123, N.v22123.
  unfold R.v6, N.v6.
  rewrite ?node_22122.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22124 (s : N.State) (i : N.Inputs) :
  R.v22124 (state s) (inputs i) = Zmod.unsigned (N.v22124 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22124 s i)) at 1.
  unfold R.v22124, N.v22124.
  rewrite ?node_7947.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22125 (s : N.State) (i : N.Inputs) :
  R.v22125 (state s) (inputs i) = Zmod.unsigned (N.v22125 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22125 s i)) at 1.
  unfold R.v22125, N.v22125.
  unfold R.v6, N.v6.
  rewrite ?node_8065.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22126 (s : N.State) (i : N.Inputs) :
  R.v22126 (state s) (inputs i) = Zmod.unsigned (N.v22126 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22126 s i)) at 1.
  unfold R.v22126, N.v22126.
  unfold R.v6, N.v6.
  rewrite ?node_8116.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22127 (s : N.State) (i : N.Inputs) :
  R.v22127 (state s) (inputs i) = Zmod.unsigned (N.v22127 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22127 s i)) at 1.
  unfold R.v22127, N.v22127.
  rewrite ?node_22124.
  rewrite ?node_22125.
  rewrite ?node_22126.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22128 (s : N.State) (i : N.Inputs) :
  R.v22128 (state s) (inputs i) = Zmod.unsigned (N.v22128 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22128 s i)) at 1.
  unfold R.v22128, N.v22128.
  rewrite ?node_22123.
  rewrite ?node_22127.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22129 (s : N.State) (i : N.Inputs) :
  R.v22129 (state s) (inputs i) = Zmod.unsigned (N.v22129 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22129 s i)) at 1.
  unfold R.v22129, N.v22129.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22130 (s : N.State) (i : N.Inputs) :
  R.v22130 (state s) (inputs i) = Zmod.unsigned (N.v22130 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22130 s i)) at 1.
  unfold R.v22130, N.v22130.
  unfold R.v16463, N.v16463.
  rewrite !state_r629_nr_5F629.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r629_nr_5F629 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22131 (s : N.State) (i : N.Inputs) :
  R.v22131 (state s) (inputs i) = Zmod.unsigned (N.v22131 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22131 s i)) at 1.
  unfold R.v22131, N.v22131.
  unfold R.v6, N.v6.
  rewrite !state_r628_nr_5F628.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r628_nr_5F628 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22132 (s : N.State) (i : N.Inputs) :
  R.v22132 (state s) (inputs i) = Zmod.unsigned (N.v22132 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22132 s i)) at 1.
  unfold R.v22132, N.v22132.
  unfold R.v6, N.v6.
  rewrite !state_r627_nr_5F627.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r627_nr_5F627 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22133 (s : N.State) (i : N.Inputs) :
  R.v22133 (state s) (inputs i) = Zmod.unsigned (N.v22133 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22133 s i)) at 1.
  unfold R.v22133, N.v22133.
  rewrite ?node_22131.
  rewrite ?node_22132.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22134 (s : N.State) (i : N.Inputs) :
  R.v22134 (state s) (inputs i) = Zmod.unsigned (N.v22134 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22134 s i)) at 1.
  unfold R.v22134, N.v22134.
  unfold R.v16484, N.v16484.
  rewrite ?node_22133.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22135 (s : N.State) (i : N.Inputs) :
  R.v22135 (state s) (inputs i) = Zmod.unsigned (N.v22135 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22135 s i)) at 1.
  unfold R.v22135, N.v22135.
  rewrite ?node_22130.
  rewrite ?node_22134.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22136 (s : N.State) (i : N.Inputs) :
  R.v22136 (state s) (inputs i) = Zmod.unsigned (N.v22136 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22136 s i)) at 1.
  unfold R.v22136, N.v22136.
  unfold R.v6, N.v6.
  rewrite ?node_22135.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22137 (s : N.State) (i : N.Inputs) :
  R.v22137 (state s) (inputs i) = Zmod.unsigned (N.v22137 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22137 s i)) at 1.
  unfold R.v22137, N.v22137.
  rewrite ?node_7942.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22138 (s : N.State) (i : N.Inputs) :
  R.v22138 (state s) (inputs i) = Zmod.unsigned (N.v22138 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22138 s i)) at 1.
  unfold R.v22138, N.v22138.
  unfold R.v6, N.v6.
  rewrite ?node_8065.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22139 (s : N.State) (i : N.Inputs) :
  R.v22139 (state s) (inputs i) = Zmod.unsigned (N.v22139 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22139 s i)) at 1.
  unfold R.v22139, N.v22139.
  rewrite ?node_22137.
  rewrite ?node_22138.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22140 (s : N.State) (i : N.Inputs) :
  R.v22140 (state s) (inputs i) = Zmod.unsigned (N.v22140 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22140 s i)) at 1.
  unfold R.v22140, N.v22140.
  rewrite ?node_22136.
  rewrite ?node_22139.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22141 (s : N.State) (i : N.Inputs) :
  R.v22141 (state s) (inputs i) = Zmod.unsigned (N.v22141 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22141 s i)) at 1.
  unfold R.v22141, N.v22141.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22142 (s : N.State) (i : N.Inputs) :
  R.v22142 (state s) (inputs i) = Zmod.unsigned (N.v22142 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22142 s i)) at 1.
  unfold R.v22142, N.v22142.
  rewrite ?node_7946.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22143 (s : N.State) (i : N.Inputs) :
  R.v22143 (state s) (inputs i) = Zmod.unsigned (N.v22143 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22143 s i)) at 1.
  unfold R.v22143, N.v22143.
  unfold R.v6, N.v6.
  rewrite !state_r630_nr_5F630.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r630_nr_5F630 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22144 (s : N.State) (i : N.Inputs) :
  R.v22144 (state s) (inputs i) = Zmod.unsigned (N.v22144 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22144 s i)) at 1.
  unfold R.v22144, N.v22144.
  unfold R.v6, N.v6.
  rewrite ?node_7942.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22145 (s : N.State) (i : N.Inputs) :
  R.v22145 (state s) (inputs i) = Zmod.unsigned (N.v22145 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22145 s i)) at 1.
  unfold R.v22145, N.v22145.
  rewrite ?node_22143.
  rewrite ?node_22144.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22146 (s : N.State) (i : N.Inputs) :
  R.v22146 (state s) (inputs i) = Zmod.unsigned (N.v22146 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22146 s i)) at 1.
  unfold R.v22146, N.v22146.
  unfold R.v16484, N.v16484.
  rewrite ?node_22145.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22147 (s : N.State) (i : N.Inputs) :
  R.v22147 (state s) (inputs i) = Zmod.unsigned (N.v22147 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22147 s i)) at 1.
  unfold R.v22147, N.v22147.
  rewrite ?node_22142.
  rewrite ?node_22146.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22148 (s : N.State) (i : N.Inputs) :
  R.v22148 (state s) (inputs i) = Zmod.unsigned (N.v22148 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22148 s i)) at 1.
  unfold R.v22148, N.v22148.
  unfold R.v6, N.v6.
  rewrite ?node_22147.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22149 (s : N.State) (i : N.Inputs) :
  R.v22149 (state s) (inputs i) = Zmod.unsigned (N.v22149 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22149 s i)) at 1.
  unfold R.v22149, N.v22149.
  rewrite ?node_7947.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22150 (s : N.State) (i : N.Inputs) :
  R.v22150 (state s) (inputs i) = Zmod.unsigned (N.v22150 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22150 s i)) at 1.
  unfold R.v22150, N.v22150.
  unfold R.v6, N.v6.
  rewrite ?node_8116.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22151 (s : N.State) (i : N.Inputs) :
  R.v22151 (state s) (inputs i) = Zmod.unsigned (N.v22151 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22151 s i)) at 1.
  unfold R.v22151, N.v22151.
  rewrite ?node_22149.
  rewrite ?node_22150.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22152 (s : N.State) (i : N.Inputs) :
  R.v22152 (state s) (inputs i) = Zmod.unsigned (N.v22152 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22152 s i)) at 1.
  unfold R.v22152, N.v22152.
  rewrite ?node_22148.
  rewrite ?node_22151.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22153 (s : N.State) (i : N.Inputs) :
  R.v22153 (state s) (inputs i) = Zmod.unsigned (N.v22153 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22153 s i)) at 1.
  unfold R.v22153, N.v22153.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22154 (s : N.State) (i : N.Inputs) :
  R.v22154 (state s) (inputs i) = Zmod.unsigned (N.v22154 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22154 s i)) at 1.
  unfold R.v22154, N.v22154.
  rewrite ?node_7954.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22155 (s : N.State) (i : N.Inputs) :
  R.v22155 (state s) (inputs i) = Zmod.unsigned (N.v22155 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22155 s i)) at 1.
  unfold R.v22155, N.v22155.
  unfold R.v16463, N.v16463.
  rewrite !state_r634_nr_5F634.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r634_nr_5F634 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22156 (s : N.State) (i : N.Inputs) :
  R.v22156 (state s) (inputs i) = Zmod.unsigned (N.v22156 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22156 s i)) at 1.
  unfold R.v22156, N.v22156.
  unfold R.v16463, N.v16463.
  rewrite !state_r633_nr_5F633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r633_nr_5F633 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22157 (s : N.State) (i : N.Inputs) :
  R.v22157 (state s) (inputs i) = Zmod.unsigned (N.v22157 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22157 s i)) at 1.
  unfold R.v22157, N.v22157.
  unfold R.v6, N.v6.
  rewrite !state_r632_nr_5F632.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r632_nr_5F632 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22158 (s : N.State) (i : N.Inputs) :
  R.v22158 (state s) (inputs i) = Zmod.unsigned (N.v22158 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22158 s i)) at 1.
  unfold R.v22158, N.v22158.
  unfold R.v6, N.v6.
  rewrite !state_r631_nr_5F631.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r631_nr_5F631 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22159 (s : N.State) (i : N.Inputs) :
  R.v22159 (state s) (inputs i) = Zmod.unsigned (N.v22159 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22159 s i)) at 1.
  unfold R.v22159, N.v22159.
  rewrite ?node_22157.
  rewrite ?node_22158.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22160 (s : N.State) (i : N.Inputs) :
  R.v22160 (state s) (inputs i) = Zmod.unsigned (N.v22160 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22160 s i)) at 1.
  unfold R.v22160, N.v22160.
  unfold R.v16484, N.v16484.
  rewrite ?node_22159.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22161 (s : N.State) (i : N.Inputs) :
  R.v22161 (state s) (inputs i) = Zmod.unsigned (N.v22161 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22161 s i)) at 1.
  unfold R.v22161, N.v22161.
  rewrite ?node_22154.
  rewrite ?node_22155.
  rewrite ?node_22156.
  rewrite ?node_22160.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22162 (s : N.State) (i : N.Inputs) :
  R.v22162 (state s) (inputs i) = Zmod.unsigned (N.v22162 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22162 s i)) at 1.
  unfold R.v22162, N.v22162.
  unfold R.v6, N.v6.
  rewrite ?node_22161.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22163 (s : N.State) (i : N.Inputs) :
  R.v22163 (state s) (inputs i) = Zmod.unsigned (N.v22163 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22163 s i)) at 1.
  unfold R.v22163, N.v22163.
  rewrite ?node_7955.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22164 (s : N.State) (i : N.Inputs) :
  R.v22164 (state s) (inputs i) = Zmod.unsigned (N.v22164 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22164 s i)) at 1.
  unfold R.v22164, N.v22164.
  unfold R.v6, N.v6.
  rewrite ?node_8073.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22165 (s : N.State) (i : N.Inputs) :
  R.v22165 (state s) (inputs i) = Zmod.unsigned (N.v22165 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22165 s i)) at 1.
  unfold R.v22165, N.v22165.
  unfold R.v6, N.v6.
  rewrite ?node_8119.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22166 (s : N.State) (i : N.Inputs) :
  R.v22166 (state s) (inputs i) = Zmod.unsigned (N.v22166 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22166 s i)) at 1.
  unfold R.v22166, N.v22166.
  rewrite ?node_22163.
  rewrite ?node_22164.
  rewrite ?node_22165.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22167 (s : N.State) (i : N.Inputs) :
  R.v22167 (state s) (inputs i) = Zmod.unsigned (N.v22167 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22167 s i)) at 1.
  unfold R.v22167, N.v22167.
  rewrite ?node_22162.
  rewrite ?node_22166.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22168 (s : N.State) (i : N.Inputs) :
  R.v22168 (state s) (inputs i) = Zmod.unsigned (N.v22168 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22168 s i)) at 1.
  unfold R.v22168, N.v22168.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22169 (s : N.State) (i : N.Inputs) :
  R.v22169 (state s) (inputs i) = Zmod.unsigned (N.v22169 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22169 s i)) at 1.
  unfold R.v22169, N.v22169.
  unfold R.v16463, N.v16463.
  rewrite !state_r633_nr_5F633.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r633_nr_5F633 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22170 (s : N.State) (i : N.Inputs) :
  R.v22170 (state s) (inputs i) = Zmod.unsigned (N.v22170 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22170 s i)) at 1.
  unfold R.v22170, N.v22170.
  unfold R.v6, N.v6.
  rewrite !state_r632_nr_5F632.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r632_nr_5F632 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22171 (s : N.State) (i : N.Inputs) :
  R.v22171 (state s) (inputs i) = Zmod.unsigned (N.v22171 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22171 s i)) at 1.
  unfold R.v22171, N.v22171.
  unfold R.v6, N.v6.
  rewrite !state_r631_nr_5F631.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r631_nr_5F631 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22172 (s : N.State) (i : N.Inputs) :
  R.v22172 (state s) (inputs i) = Zmod.unsigned (N.v22172 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22172 s i)) at 1.
  unfold R.v22172, N.v22172.
  rewrite ?node_22170.
  rewrite ?node_22171.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22173 (s : N.State) (i : N.Inputs) :
  R.v22173 (state s) (inputs i) = Zmod.unsigned (N.v22173 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22173 s i)) at 1.
  unfold R.v22173, N.v22173.
  unfold R.v16484, N.v16484.
  rewrite ?node_22172.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22174 (s : N.State) (i : N.Inputs) :
  R.v22174 (state s) (inputs i) = Zmod.unsigned (N.v22174 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22174 s i)) at 1.
  unfold R.v22174, N.v22174.
  rewrite ?node_22169.
  rewrite ?node_22173.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22175 (s : N.State) (i : N.Inputs) :
  R.v22175 (state s) (inputs i) = Zmod.unsigned (N.v22175 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22175 s i)) at 1.
  unfold R.v22175, N.v22175.
  unfold R.v6, N.v6.
  rewrite ?node_22174.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22176 (s : N.State) (i : N.Inputs) :
  R.v22176 (state s) (inputs i) = Zmod.unsigned (N.v22176 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22176 s i)) at 1.
  unfold R.v22176, N.v22176.
  rewrite ?node_7950.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22177 (s : N.State) (i : N.Inputs) :
  R.v22177 (state s) (inputs i) = Zmod.unsigned (N.v22177 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22177 s i)) at 1.
  unfold R.v22177, N.v22177.
  unfold R.v6, N.v6.
  rewrite ?node_8073.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22178 (s : N.State) (i : N.Inputs) :
  R.v22178 (state s) (inputs i) = Zmod.unsigned (N.v22178 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22178 s i)) at 1.
  unfold R.v22178, N.v22178.
  rewrite ?node_22176.
  rewrite ?node_22177.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22179 (s : N.State) (i : N.Inputs) :
  R.v22179 (state s) (inputs i) = Zmod.unsigned (N.v22179 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22179 s i)) at 1.
  unfold R.v22179, N.v22179.
  rewrite ?node_22175.
  rewrite ?node_22178.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22180 (s : N.State) (i : N.Inputs) :
  R.v22180 (state s) (inputs i) = Zmod.unsigned (N.v22180 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22180 s i)) at 1.
  unfold R.v22180, N.v22180.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22181 (s : N.State) (i : N.Inputs) :
  R.v22181 (state s) (inputs i) = Zmod.unsigned (N.v22181 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22181 s i)) at 1.
  unfold R.v22181, N.v22181.
  rewrite ?node_7954.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22182 (s : N.State) (i : N.Inputs) :
  R.v22182 (state s) (inputs i) = Zmod.unsigned (N.v22182 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22182 s i)) at 1.
  unfold R.v22182, N.v22182.
  unfold R.v6, N.v6.
  rewrite !state_r634_nr_5F634.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r634_nr_5F634 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22183 (s : N.State) (i : N.Inputs) :
  R.v22183 (state s) (inputs i) = Zmod.unsigned (N.v22183 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22183 s i)) at 1.
  unfold R.v22183, N.v22183.
  unfold R.v6, N.v6.
  rewrite ?node_7950.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22184 (s : N.State) (i : N.Inputs) :
  R.v22184 (state s) (inputs i) = Zmod.unsigned (N.v22184 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22184 s i)) at 1.
  unfold R.v22184, N.v22184.
  rewrite ?node_22182.
  rewrite ?node_22183.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22185 (s : N.State) (i : N.Inputs) :
  R.v22185 (state s) (inputs i) = Zmod.unsigned (N.v22185 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22185 s i)) at 1.
  unfold R.v22185, N.v22185.
  unfold R.v16484, N.v16484.
  rewrite ?node_22184.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22186 (s : N.State) (i : N.Inputs) :
  R.v22186 (state s) (inputs i) = Zmod.unsigned (N.v22186 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22186 s i)) at 1.
  unfold R.v22186, N.v22186.
  rewrite ?node_22181.
  rewrite ?node_22185.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22187 (s : N.State) (i : N.Inputs) :
  R.v22187 (state s) (inputs i) = Zmod.unsigned (N.v22187 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22187 s i)) at 1.
  unfold R.v22187, N.v22187.
  unfold R.v6, N.v6.
  rewrite ?node_22186.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22188 (s : N.State) (i : N.Inputs) :
  R.v22188 (state s) (inputs i) = Zmod.unsigned (N.v22188 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22188 s i)) at 1.
  unfold R.v22188, N.v22188.
  rewrite ?node_7955.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22189 (s : N.State) (i : N.Inputs) :
  R.v22189 (state s) (inputs i) = Zmod.unsigned (N.v22189 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22189 s i)) at 1.
  unfold R.v22189, N.v22189.
  unfold R.v6, N.v6.
  rewrite ?node_8119.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22190 (s : N.State) (i : N.Inputs) :
  R.v22190 (state s) (inputs i) = Zmod.unsigned (N.v22190 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22190 s i)) at 1.
  unfold R.v22190, N.v22190.
  rewrite ?node_22188.
  rewrite ?node_22189.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22191 (s : N.State) (i : N.Inputs) :
  R.v22191 (state s) (inputs i) = Zmod.unsigned (N.v22191 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22191 s i)) at 1.
  unfold R.v22191, N.v22191.
  rewrite ?node_22187.
  rewrite ?node_22190.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22192 (s : N.State) (i : N.Inputs) :
  R.v22192 (state s) (inputs i) = Zmod.unsigned (N.v22192 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22192 s i)) at 1.
  unfold R.v22192, N.v22192.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22193 (s : N.State) (i : N.Inputs) :
  R.v22193 (state s) (inputs i) = Zmod.unsigned (N.v22193 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22193 s i)) at 1.
  unfold R.v22193, N.v22193.
  rewrite ?node_7962.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22194 (s : N.State) (i : N.Inputs) :
  R.v22194 (state s) (inputs i) = Zmod.unsigned (N.v22194 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22194 s i)) at 1.
  unfold R.v22194, N.v22194.
  unfold R.v16463, N.v16463.
  rewrite !state_r638_nr_5F638.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r638_nr_5F638 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22195 (s : N.State) (i : N.Inputs) :
  R.v22195 (state s) (inputs i) = Zmod.unsigned (N.v22195 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22195 s i)) at 1.
  unfold R.v22195, N.v22195.
  unfold R.v16463, N.v16463.
  rewrite !state_r637_nr_5F637.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r637_nr_5F637 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22196 (s : N.State) (i : N.Inputs) :
  R.v22196 (state s) (inputs i) = Zmod.unsigned (N.v22196 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22196 s i)) at 1.
  unfold R.v22196, N.v22196.
  unfold R.v6, N.v6.
  rewrite !state_r636_nr_5F636.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r636_nr_5F636 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22197 (s : N.State) (i : N.Inputs) :
  R.v22197 (state s) (inputs i) = Zmod.unsigned (N.v22197 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22197 s i)) at 1.
  unfold R.v22197, N.v22197.
  unfold R.v6, N.v6.
  rewrite !state_r635_nr_5F635.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r635_nr_5F635 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22198 (s : N.State) (i : N.Inputs) :
  R.v22198 (state s) (inputs i) = Zmod.unsigned (N.v22198 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22198 s i)) at 1.
  unfold R.v22198, N.v22198.
  rewrite ?node_22196.
  rewrite ?node_22197.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22199 (s : N.State) (i : N.Inputs) :
  R.v22199 (state s) (inputs i) = Zmod.unsigned (N.v22199 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22199 s i)) at 1.
  unfold R.v22199, N.v22199.
  unfold R.v16484, N.v16484.
  rewrite ?node_22198.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22200 (s : N.State) (i : N.Inputs) :
  R.v22200 (state s) (inputs i) = Zmod.unsigned (N.v22200 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22200 s i)) at 1.
  unfold R.v22200, N.v22200.
  rewrite ?node_22193.
  rewrite ?node_22194.
  rewrite ?node_22195.
  rewrite ?node_22199.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22201 (s : N.State) (i : N.Inputs) :
  R.v22201 (state s) (inputs i) = Zmod.unsigned (N.v22201 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22201 s i)) at 1.
  unfold R.v22201, N.v22201.
  unfold R.v6, N.v6.
  rewrite ?node_22200.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22202 (s : N.State) (i : N.Inputs) :
  R.v22202 (state s) (inputs i) = Zmod.unsigned (N.v22202 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22202 s i)) at 1.
  unfold R.v22202, N.v22202.
  rewrite ?node_7963.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22203 (s : N.State) (i : N.Inputs) :
  R.v22203 (state s) (inputs i) = Zmod.unsigned (N.v22203 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22203 s i)) at 1.
  unfold R.v22203, N.v22203.
  unfold R.v6, N.v6.
  rewrite ?node_8081.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22204 (s : N.State) (i : N.Inputs) :
  R.v22204 (state s) (inputs i) = Zmod.unsigned (N.v22204 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22204 s i)) at 1.
  unfold R.v22204, N.v22204.
  unfold R.v6, N.v6.
  rewrite ?node_8123.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22205 (s : N.State) (i : N.Inputs) :
  R.v22205 (state s) (inputs i) = Zmod.unsigned (N.v22205 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22205 s i)) at 1.
  unfold R.v22205, N.v22205.
  rewrite ?node_22202.
  rewrite ?node_22203.
  rewrite ?node_22204.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22206 (s : N.State) (i : N.Inputs) :
  R.v22206 (state s) (inputs i) = Zmod.unsigned (N.v22206 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22206 s i)) at 1.
  unfold R.v22206, N.v22206.
  rewrite ?node_22201.
  rewrite ?node_22205.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22207 (s : N.State) (i : N.Inputs) :
  R.v22207 (state s) (inputs i) = Zmod.unsigned (N.v22207 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22207 s i)) at 1.
  unfold R.v22207, N.v22207.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22208 (s : N.State) (i : N.Inputs) :
  R.v22208 (state s) (inputs i) = Zmod.unsigned (N.v22208 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22208 s i)) at 1.
  unfold R.v22208, N.v22208.
  unfold R.v16463, N.v16463.
  rewrite !state_r637_nr_5F637.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r637_nr_5F637 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22209 (s : N.State) (i : N.Inputs) :
  R.v22209 (state s) (inputs i) = Zmod.unsigned (N.v22209 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22209 s i)) at 1.
  unfold R.v22209, N.v22209.
  unfold R.v6, N.v6.
  rewrite !state_r636_nr_5F636.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r636_nr_5F636 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22210 (s : N.State) (i : N.Inputs) :
  R.v22210 (state s) (inputs i) = Zmod.unsigned (N.v22210 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22210 s i)) at 1.
  unfold R.v22210, N.v22210.
  unfold R.v6, N.v6.
  rewrite !state_r635_nr_5F635.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r635_nr_5F635 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22211 (s : N.State) (i : N.Inputs) :
  R.v22211 (state s) (inputs i) = Zmod.unsigned (N.v22211 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22211 s i)) at 1.
  unfold R.v22211, N.v22211.
  rewrite ?node_22209.
  rewrite ?node_22210.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22212 (s : N.State) (i : N.Inputs) :
  R.v22212 (state s) (inputs i) = Zmod.unsigned (N.v22212 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22212 s i)) at 1.
  unfold R.v22212, N.v22212.
  unfold R.v16484, N.v16484.
  rewrite ?node_22211.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22213 (s : N.State) (i : N.Inputs) :
  R.v22213 (state s) (inputs i) = Zmod.unsigned (N.v22213 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22213 s i)) at 1.
  unfold R.v22213, N.v22213.
  rewrite ?node_22208.
  rewrite ?node_22212.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22214 (s : N.State) (i : N.Inputs) :
  R.v22214 (state s) (inputs i) = Zmod.unsigned (N.v22214 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22214 s i)) at 1.
  unfold R.v22214, N.v22214.
  unfold R.v6, N.v6.
  rewrite ?node_22213.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22215 (s : N.State) (i : N.Inputs) :
  R.v22215 (state s) (inputs i) = Zmod.unsigned (N.v22215 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22215 s i)) at 1.
  unfold R.v22215, N.v22215.
  rewrite ?node_7958.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22216 (s : N.State) (i : N.Inputs) :
  R.v22216 (state s) (inputs i) = Zmod.unsigned (N.v22216 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22216 s i)) at 1.
  unfold R.v22216, N.v22216.
  unfold R.v6, N.v6.
  rewrite ?node_8081.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22217 (s : N.State) (i : N.Inputs) :
  R.v22217 (state s) (inputs i) = Zmod.unsigned (N.v22217 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22217 s i)) at 1.
  unfold R.v22217, N.v22217.
  rewrite ?node_22215.
  rewrite ?node_22216.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22218 (s : N.State) (i : N.Inputs) :
  R.v22218 (state s) (inputs i) = Zmod.unsigned (N.v22218 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22218 s i)) at 1.
  unfold R.v22218, N.v22218.
  rewrite ?node_22214.
  rewrite ?node_22217.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22219 (s : N.State) (i : N.Inputs) :
  R.v22219 (state s) (inputs i) = Zmod.unsigned (N.v22219 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22219 s i)) at 1.
  unfold R.v22219, N.v22219.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22220 (s : N.State) (i : N.Inputs) :
  R.v22220 (state s) (inputs i) = Zmod.unsigned (N.v22220 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22220 s i)) at 1.
  unfold R.v22220, N.v22220.
  rewrite ?node_7962.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22221 (s : N.State) (i : N.Inputs) :
  R.v22221 (state s) (inputs i) = Zmod.unsigned (N.v22221 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22221 s i)) at 1.
  unfold R.v22221, N.v22221.
  unfold R.v6, N.v6.
  rewrite !state_r638_nr_5F638.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r638_nr_5F638 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22222 (s : N.State) (i : N.Inputs) :
  R.v22222 (state s) (inputs i) = Zmod.unsigned (N.v22222 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22222 s i)) at 1.
  unfold R.v22222, N.v22222.
  unfold R.v6, N.v6.
  rewrite ?node_7958.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22223 (s : N.State) (i : N.Inputs) :
  R.v22223 (state s) (inputs i) = Zmod.unsigned (N.v22223 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22223 s i)) at 1.
  unfold R.v22223, N.v22223.
  rewrite ?node_22221.
  rewrite ?node_22222.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22224 (s : N.State) (i : N.Inputs) :
  R.v22224 (state s) (inputs i) = Zmod.unsigned (N.v22224 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22224 s i)) at 1.
  unfold R.v22224, N.v22224.
  unfold R.v16484, N.v16484.
  rewrite ?node_22223.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22225 (s : N.State) (i : N.Inputs) :
  R.v22225 (state s) (inputs i) = Zmod.unsigned (N.v22225 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22225 s i)) at 1.
  unfold R.v22225, N.v22225.
  rewrite ?node_22220.
  rewrite ?node_22224.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22226 (s : N.State) (i : N.Inputs) :
  R.v22226 (state s) (inputs i) = Zmod.unsigned (N.v22226 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22226 s i)) at 1.
  unfold R.v22226, N.v22226.
  unfold R.v6, N.v6.
  rewrite ?node_22225.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22227 (s : N.State) (i : N.Inputs) :
  R.v22227 (state s) (inputs i) = Zmod.unsigned (N.v22227 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22227 s i)) at 1.
  unfold R.v22227, N.v22227.
  rewrite ?node_7963.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22228 (s : N.State) (i : N.Inputs) :
  R.v22228 (state s) (inputs i) = Zmod.unsigned (N.v22228 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22228 s i)) at 1.
  unfold R.v22228, N.v22228.
  unfold R.v6, N.v6.
  rewrite ?node_8123.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22229 (s : N.State) (i : N.Inputs) :
  R.v22229 (state s) (inputs i) = Zmod.unsigned (N.v22229 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22229 s i)) at 1.
  unfold R.v22229, N.v22229.
  rewrite ?node_22227.
  rewrite ?node_22228.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22230 (s : N.State) (i : N.Inputs) :
  R.v22230 (state s) (inputs i) = Zmod.unsigned (N.v22230 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22230 s i)) at 1.
  unfold R.v22230, N.v22230.
  rewrite ?node_22226.
  rewrite ?node_22229.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22231 (s : N.State) (i : N.Inputs) :
  R.v22231 (state s) (inputs i) = Zmod.unsigned (N.v22231 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22231 s i)) at 1.
  unfold R.v22231, N.v22231.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22232 (s : N.State) (i : N.Inputs) :
  R.v22232 (state s) (inputs i) = Zmod.unsigned (N.v22232 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22232 s i)) at 1.
  unfold R.v22232, N.v22232.
  rewrite ?node_7974.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22233 (s : N.State) (i : N.Inputs) :
  R.v22233 (state s) (inputs i) = Zmod.unsigned (N.v22233 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22233 s i)) at 1.
  unfold R.v22233, N.v22233.
  unfold R.v16463, N.v16463.
  rewrite !state_r642_nr_5F642.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r642_nr_5F642 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22234 (s : N.State) (i : N.Inputs) :
  R.v22234 (state s) (inputs i) = Zmod.unsigned (N.v22234 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22234 s i)) at 1.
  unfold R.v22234, N.v22234.
  unfold R.v16463, N.v16463.
  rewrite !state_r641_nr_5F641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r641_nr_5F641 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22235 (s : N.State) (i : N.Inputs) :
  R.v22235 (state s) (inputs i) = Zmod.unsigned (N.v22235 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22235 s i)) at 1.
  unfold R.v22235, N.v22235.
  unfold R.v6, N.v6.
  rewrite !state_r640_nr_5F640.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r640_nr_5F640 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22236 (s : N.State) (i : N.Inputs) :
  R.v22236 (state s) (inputs i) = Zmod.unsigned (N.v22236 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22236 s i)) at 1.
  unfold R.v22236, N.v22236.
  unfold R.v6, N.v6.
  rewrite !state_r639_nr_5F639.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r639_nr_5F639 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22237 (s : N.State) (i : N.Inputs) :
  R.v22237 (state s) (inputs i) = Zmod.unsigned (N.v22237 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22237 s i)) at 1.
  unfold R.v22237, N.v22237.
  rewrite ?node_22235.
  rewrite ?node_22236.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22238 (s : N.State) (i : N.Inputs) :
  R.v22238 (state s) (inputs i) = Zmod.unsigned (N.v22238 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22238 s i)) at 1.
  unfold R.v22238, N.v22238.
  unfold R.v16484, N.v16484.
  rewrite ?node_22237.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22239 (s : N.State) (i : N.Inputs) :
  R.v22239 (state s) (inputs i) = Zmod.unsigned (N.v22239 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22239 s i)) at 1.
  unfold R.v22239, N.v22239.
  rewrite ?node_22232.
  rewrite ?node_22233.
  rewrite ?node_22234.
  rewrite ?node_22238.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22240 (s : N.State) (i : N.Inputs) :
  R.v22240 (state s) (inputs i) = Zmod.unsigned (N.v22240 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22240 s i)) at 1.
  unfold R.v22240, N.v22240.
  unfold R.v6, N.v6.
  rewrite ?node_22239.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22241 (s : N.State) (i : N.Inputs) :
  R.v22241 (state s) (inputs i) = Zmod.unsigned (N.v22241 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22241 s i)) at 1.
  unfold R.v22241, N.v22241.
  rewrite ?node_7975.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22242 (s : N.State) (i : N.Inputs) :
  R.v22242 (state s) (inputs i) = Zmod.unsigned (N.v22242 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22242 s i)) at 1.
  unfold R.v22242, N.v22242.
  unfold R.v6, N.v6.
  rewrite ?node_8093.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22243 (s : N.State) (i : N.Inputs) :
  R.v22243 (state s) (inputs i) = Zmod.unsigned (N.v22243 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22243 s i)) at 1.
  unfold R.v22243, N.v22243.
  unfold R.v6, N.v6.
  rewrite ?node_8127.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22244 (s : N.State) (i : N.Inputs) :
  R.v22244 (state s) (inputs i) = Zmod.unsigned (N.v22244 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22244 s i)) at 1.
  unfold R.v22244, N.v22244.
  rewrite ?node_22241.
  rewrite ?node_22242.
  rewrite ?node_22243.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22245 (s : N.State) (i : N.Inputs) :
  R.v22245 (state s) (inputs i) = Zmod.unsigned (N.v22245 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22245 s i)) at 1.
  unfold R.v22245, N.v22245.
  rewrite ?node_22240.
  rewrite ?node_22244.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22246 (s : N.State) (i : N.Inputs) :
  R.v22246 (state s) (inputs i) = Zmod.unsigned (N.v22246 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22246 s i)) at 1.
  unfold R.v22246, N.v22246.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22247 (s : N.State) (i : N.Inputs) :
  R.v22247 (state s) (inputs i) = Zmod.unsigned (N.v22247 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22247 s i)) at 1.
  unfold R.v22247, N.v22247.
  unfold R.v16463, N.v16463.
  rewrite !state_r641_nr_5F641.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r641_nr_5F641 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22248 (s : N.State) (i : N.Inputs) :
  R.v22248 (state s) (inputs i) = Zmod.unsigned (N.v22248 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22248 s i)) at 1.
  unfold R.v22248, N.v22248.
  unfold R.v6, N.v6.
  rewrite !state_r640_nr_5F640.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r640_nr_5F640 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22249 (s : N.State) (i : N.Inputs) :
  R.v22249 (state s) (inputs i) = Zmod.unsigned (N.v22249 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22249 s i)) at 1.
  unfold R.v22249, N.v22249.
  unfold R.v6, N.v6.
  rewrite !state_r639_nr_5F639.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r639_nr_5F639 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22250 (s : N.State) (i : N.Inputs) :
  R.v22250 (state s) (inputs i) = Zmod.unsigned (N.v22250 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22250 s i)) at 1.
  unfold R.v22250, N.v22250.
  rewrite ?node_22248.
  rewrite ?node_22249.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22251 (s : N.State) (i : N.Inputs) :
  R.v22251 (state s) (inputs i) = Zmod.unsigned (N.v22251 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22251 s i)) at 1.
  unfold R.v22251, N.v22251.
  unfold R.v16484, N.v16484.
  rewrite ?node_22250.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22252 (s : N.State) (i : N.Inputs) :
  R.v22252 (state s) (inputs i) = Zmod.unsigned (N.v22252 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22252 s i)) at 1.
  unfold R.v22252, N.v22252.
  rewrite ?node_22247.
  rewrite ?node_22251.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22253 (s : N.State) (i : N.Inputs) :
  R.v22253 (state s) (inputs i) = Zmod.unsigned (N.v22253 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22253 s i)) at 1.
  unfold R.v22253, N.v22253.
  unfold R.v6, N.v6.
  rewrite ?node_22252.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22254 (s : N.State) (i : N.Inputs) :
  R.v22254 (state s) (inputs i) = Zmod.unsigned (N.v22254 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22254 s i)) at 1.
  unfold R.v22254, N.v22254.
  rewrite ?node_7970.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22255 (s : N.State) (i : N.Inputs) :
  R.v22255 (state s) (inputs i) = Zmod.unsigned (N.v22255 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22255 s i)) at 1.
  unfold R.v22255, N.v22255.
  unfold R.v6, N.v6.
  rewrite ?node_8093.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22256 (s : N.State) (i : N.Inputs) :
  R.v22256 (state s) (inputs i) = Zmod.unsigned (N.v22256 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22256 s i)) at 1.
  unfold R.v22256, N.v22256.
  rewrite ?node_22254.
  rewrite ?node_22255.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22257 (s : N.State) (i : N.Inputs) :
  R.v22257 (state s) (inputs i) = Zmod.unsigned (N.v22257 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22257 s i)) at 1.
  unfold R.v22257, N.v22257.
  rewrite ?node_22253.
  rewrite ?node_22256.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22258 (s : N.State) (i : N.Inputs) :
  R.v22258 (state s) (inputs i) = Zmod.unsigned (N.v22258 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22258 s i)) at 1.
  unfold R.v22258, N.v22258.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22259 (s : N.State) (i : N.Inputs) :
  R.v22259 (state s) (inputs i) = Zmod.unsigned (N.v22259 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22259 s i)) at 1.
  unfold R.v22259, N.v22259.
  rewrite ?node_7974.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22260 (s : N.State) (i : N.Inputs) :
  R.v22260 (state s) (inputs i) = Zmod.unsigned (N.v22260 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22260 s i)) at 1.
  unfold R.v22260, N.v22260.
  unfold R.v6, N.v6.
  rewrite !state_r642_nr_5F642.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r642_nr_5F642 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22261 (s : N.State) (i : N.Inputs) :
  R.v22261 (state s) (inputs i) = Zmod.unsigned (N.v22261 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22261 s i)) at 1.
  unfold R.v22261, N.v22261.
  unfold R.v6, N.v6.
  rewrite ?node_7970.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22262 (s : N.State) (i : N.Inputs) :
  R.v22262 (state s) (inputs i) = Zmod.unsigned (N.v22262 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22262 s i)) at 1.
  unfold R.v22262, N.v22262.
  rewrite ?node_22260.
  rewrite ?node_22261.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22263 (s : N.State) (i : N.Inputs) :
  R.v22263 (state s) (inputs i) = Zmod.unsigned (N.v22263 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22263 s i)) at 1.
  unfold R.v22263, N.v22263.
  unfold R.v16484, N.v16484.
  rewrite ?node_22262.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22264 (s : N.State) (i : N.Inputs) :
  R.v22264 (state s) (inputs i) = Zmod.unsigned (N.v22264 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22264 s i)) at 1.
  unfold R.v22264, N.v22264.
  rewrite ?node_22259.
  rewrite ?node_22263.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22265 (s : N.State) (i : N.Inputs) :
  R.v22265 (state s) (inputs i) = Zmod.unsigned (N.v22265 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22265 s i)) at 1.
  unfold R.v22265, N.v22265.
  unfold R.v6, N.v6.
  rewrite ?node_22264.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22266 (s : N.State) (i : N.Inputs) :
  R.v22266 (state s) (inputs i) = Zmod.unsigned (N.v22266 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22266 s i)) at 1.
  unfold R.v22266, N.v22266.
  rewrite ?node_7975.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22267 (s : N.State) (i : N.Inputs) :
  R.v22267 (state s) (inputs i) = Zmod.unsigned (N.v22267 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22267 s i)) at 1.
  unfold R.v22267, N.v22267.
  unfold R.v6, N.v6.
  rewrite ?node_8127.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22268 (s : N.State) (i : N.Inputs) :
  R.v22268 (state s) (inputs i) = Zmod.unsigned (N.v22268 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22268 s i)) at 1.
  unfold R.v22268, N.v22268.
  rewrite ?node_22266.
  rewrite ?node_22267.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22269 (s : N.State) (i : N.Inputs) :
  R.v22269 (state s) (inputs i) = Zmod.unsigned (N.v22269 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22269 s i)) at 1.
  unfold R.v22269, N.v22269.
  rewrite ?node_22265.
  rewrite ?node_22268.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22270 (s : N.State) (i : N.Inputs) :
  R.v22270 (state s) (inputs i) = Zmod.unsigned (N.v22270 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22270 s i)) at 1.
  unfold R.v22270, N.v22270.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22271 (s : N.State) (i : N.Inputs) :
  R.v22271 (state s) (inputs i) = Zmod.unsigned (N.v22271 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22271 s i)) at 1.
  unfold R.v22271, N.v22271.
  rewrite ?node_7981.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22272 (s : N.State) (i : N.Inputs) :
  R.v22272 (state s) (inputs i) = Zmod.unsigned (N.v22272 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22272 s i)) at 1.
  unfold R.v22272, N.v22272.
  unfold R.v16463, N.v16463.
  rewrite !state_r646_nr_5F646.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r646_nr_5F646 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22273 (s : N.State) (i : N.Inputs) :
  R.v22273 (state s) (inputs i) = Zmod.unsigned (N.v22273 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22273 s i)) at 1.
  unfold R.v22273, N.v22273.
  unfold R.v16463, N.v16463.
  rewrite !state_r645_nr_5F645.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r645_nr_5F645 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22274 (s : N.State) (i : N.Inputs) :
  R.v22274 (state s) (inputs i) = Zmod.unsigned (N.v22274 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22274 s i)) at 1.
  unfold R.v22274, N.v22274.
  unfold R.v6, N.v6.
  rewrite !state_r644_nr_5F644.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r644_nr_5F644 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22275 (s : N.State) (i : N.Inputs) :
  R.v22275 (state s) (inputs i) = Zmod.unsigned (N.v22275 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22275 s i)) at 1.
  unfold R.v22275, N.v22275.
  unfold R.v6, N.v6.
  rewrite !state_r643_nr_5F643.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r643_nr_5F643 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22276 (s : N.State) (i : N.Inputs) :
  R.v22276 (state s) (inputs i) = Zmod.unsigned (N.v22276 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22276 s i)) at 1.
  unfold R.v22276, N.v22276.
  rewrite ?node_22274.
  rewrite ?node_22275.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22277 (s : N.State) (i : N.Inputs) :
  R.v22277 (state s) (inputs i) = Zmod.unsigned (N.v22277 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22277 s i)) at 1.
  unfold R.v22277, N.v22277.
  unfold R.v16484, N.v16484.
  rewrite ?node_22276.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22278 (s : N.State) (i : N.Inputs) :
  R.v22278 (state s) (inputs i) = Zmod.unsigned (N.v22278 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22278 s i)) at 1.
  unfold R.v22278, N.v22278.
  rewrite ?node_22271.
  rewrite ?node_22272.
  rewrite ?node_22273.
  rewrite ?node_22277.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22279 (s : N.State) (i : N.Inputs) :
  R.v22279 (state s) (inputs i) = Zmod.unsigned (N.v22279 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22279 s i)) at 1.
  unfold R.v22279, N.v22279.
  unfold R.v6, N.v6.
  rewrite ?node_22278.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22280 (s : N.State) (i : N.Inputs) :
  R.v22280 (state s) (inputs i) = Zmod.unsigned (N.v22280 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22280 s i)) at 1.
  unfold R.v22280, N.v22280.
  rewrite ?node_7982.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22281 (s : N.State) (i : N.Inputs) :
  R.v22281 (state s) (inputs i) = Zmod.unsigned (N.v22281 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22281 s i)) at 1.
  unfold R.v22281, N.v22281.
  unfold R.v6, N.v6.
  rewrite ?node_8100.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22282 (s : N.State) (i : N.Inputs) :
  R.v22282 (state s) (inputs i) = Zmod.unsigned (N.v22282 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22282 s i)) at 1.
  unfold R.v22282, N.v22282.
  unfold R.v6, N.v6.
  rewrite ?node_8136.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22283 (s : N.State) (i : N.Inputs) :
  R.v22283 (state s) (inputs i) = Zmod.unsigned (N.v22283 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22283 s i)) at 1.
  unfold R.v22283, N.v22283.
  rewrite ?node_22280.
  rewrite ?node_22281.
  rewrite ?node_22282.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22284 (s : N.State) (i : N.Inputs) :
  R.v22284 (state s) (inputs i) = Zmod.unsigned (N.v22284 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22284 s i)) at 1.
  unfold R.v22284, N.v22284.
  rewrite ?node_22279.
  rewrite ?node_22283.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22285 (s : N.State) (i : N.Inputs) :
  R.v22285 (state s) (inputs i) = Zmod.unsigned (N.v22285 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22285 s i)) at 1.
  unfold R.v22285, N.v22285.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22286 (s : N.State) (i : N.Inputs) :
  R.v22286 (state s) (inputs i) = Zmod.unsigned (N.v22286 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22286 s i)) at 1.
  unfold R.v22286, N.v22286.
  unfold R.v16463, N.v16463.
  rewrite !state_r645_nr_5F645.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r645_nr_5F645 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22287 (s : N.State) (i : N.Inputs) :
  R.v22287 (state s) (inputs i) = Zmod.unsigned (N.v22287 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22287 s i)) at 1.
  unfold R.v22287, N.v22287.
  unfold R.v6, N.v6.
  rewrite !state_r644_nr_5F644.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r644_nr_5F644 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22288 (s : N.State) (i : N.Inputs) :
  R.v22288 (state s) (inputs i) = Zmod.unsigned (N.v22288 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22288 s i)) at 1.
  unfold R.v22288, N.v22288.
  unfold R.v6, N.v6.
  rewrite !state_r643_nr_5F643.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r643_nr_5F643 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22289 (s : N.State) (i : N.Inputs) :
  R.v22289 (state s) (inputs i) = Zmod.unsigned (N.v22289 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22289 s i)) at 1.
  unfold R.v22289, N.v22289.
  rewrite ?node_22287.
  rewrite ?node_22288.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22290 (s : N.State) (i : N.Inputs) :
  R.v22290 (state s) (inputs i) = Zmod.unsigned (N.v22290 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22290 s i)) at 1.
  unfold R.v22290, N.v22290.
  unfold R.v16484, N.v16484.
  rewrite ?node_22289.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22291 (s : N.State) (i : N.Inputs) :
  R.v22291 (state s) (inputs i) = Zmod.unsigned (N.v22291 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22291 s i)) at 1.
  unfold R.v22291, N.v22291.
  rewrite ?node_22286.
  rewrite ?node_22290.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22292 (s : N.State) (i : N.Inputs) :
  R.v22292 (state s) (inputs i) = Zmod.unsigned (N.v22292 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22292 s i)) at 1.
  unfold R.v22292, N.v22292.
  unfold R.v6, N.v6.
  rewrite ?node_22291.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22293 (s : N.State) (i : N.Inputs) :
  R.v22293 (state s) (inputs i) = Zmod.unsigned (N.v22293 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22293 s i)) at 1.
  unfold R.v22293, N.v22293.
  rewrite ?node_7977.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22294 (s : N.State) (i : N.Inputs) :
  R.v22294 (state s) (inputs i) = Zmod.unsigned (N.v22294 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22294 s i)) at 1.
  unfold R.v22294, N.v22294.
  unfold R.v6, N.v6.
  rewrite ?node_8100.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22295 (s : N.State) (i : N.Inputs) :
  R.v22295 (state s) (inputs i) = Zmod.unsigned (N.v22295 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22295 s i)) at 1.
  unfold R.v22295, N.v22295.
  rewrite ?node_22293.
  rewrite ?node_22294.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22296 (s : N.State) (i : N.Inputs) :
  R.v22296 (state s) (inputs i) = Zmod.unsigned (N.v22296 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22296 s i)) at 1.
  unfold R.v22296, N.v22296.
  rewrite ?node_22292.
  rewrite ?node_22295.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22297 (s : N.State) (i : N.Inputs) :
  R.v22297 (state s) (inputs i) = Zmod.unsigned (N.v22297 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22297 s i)) at 1.
  unfold R.v22297, N.v22297.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22298 (s : N.State) (i : N.Inputs) :
  R.v22298 (state s) (inputs i) = Zmod.unsigned (N.v22298 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22298 s i)) at 1.
  unfold R.v22298, N.v22298.
  rewrite ?node_7981.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22299 (s : N.State) (i : N.Inputs) :
  R.v22299 (state s) (inputs i) = Zmod.unsigned (N.v22299 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22299 s i)) at 1.
  unfold R.v22299, N.v22299.
  unfold R.v6, N.v6.
  rewrite !state_r646_nr_5F646.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r646_nr_5F646 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22300 (s : N.State) (i : N.Inputs) :
  R.v22300 (state s) (inputs i) = Zmod.unsigned (N.v22300 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22300 s i)) at 1.
  unfold R.v22300, N.v22300.
  unfold R.v6, N.v6.
  rewrite ?node_7977.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22301 (s : N.State) (i : N.Inputs) :
  R.v22301 (state s) (inputs i) = Zmod.unsigned (N.v22301 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22301 s i)) at 1.
  unfold R.v22301, N.v22301.
  rewrite ?node_22299.
  rewrite ?node_22300.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22302 (s : N.State) (i : N.Inputs) :
  R.v22302 (state s) (inputs i) = Zmod.unsigned (N.v22302 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22302 s i)) at 1.
  unfold R.v22302, N.v22302.
  unfold R.v16484, N.v16484.
  rewrite ?node_22301.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22303 (s : N.State) (i : N.Inputs) :
  R.v22303 (state s) (inputs i) = Zmod.unsigned (N.v22303 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22303 s i)) at 1.
  unfold R.v22303, N.v22303.
  rewrite ?node_22298.
  rewrite ?node_22302.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22304 (s : N.State) (i : N.Inputs) :
  R.v22304 (state s) (inputs i) = Zmod.unsigned (N.v22304 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22304 s i)) at 1.
  unfold R.v22304, N.v22304.
  unfold R.v6, N.v6.
  rewrite ?node_22303.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22305 (s : N.State) (i : N.Inputs) :
  R.v22305 (state s) (inputs i) = Zmod.unsigned (N.v22305 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22305 s i)) at 1.
  unfold R.v22305, N.v22305.
  rewrite ?node_7982.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22306 (s : N.State) (i : N.Inputs) :
  R.v22306 (state s) (inputs i) = Zmod.unsigned (N.v22306 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22306 s i)) at 1.
  unfold R.v22306, N.v22306.
  unfold R.v6, N.v6.
  rewrite ?node_8136.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22307 (s : N.State) (i : N.Inputs) :
  R.v22307 (state s) (inputs i) = Zmod.unsigned (N.v22307 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22307 s i)) at 1.
  unfold R.v22307, N.v22307.
  rewrite ?node_22305.
  rewrite ?node_22306.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22308 (s : N.State) (i : N.Inputs) :
  R.v22308 (state s) (inputs i) = Zmod.unsigned (N.v22308 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22308 s i)) at 1.
  unfold R.v22308, N.v22308.
  rewrite ?node_22304.
  rewrite ?node_22307.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22309 (s : N.State) (i : N.Inputs) :
  R.v22309 (state s) (inputs i) = Zmod.unsigned (N.v22309 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22309 s i)) at 1.
  unfold R.v22309, N.v22309.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22310 (s : N.State) (i : N.Inputs) :
  R.v22310 (state s) (inputs i) = Zmod.unsigned (N.v22310 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22310 s i)) at 1.
  unfold R.v22310, N.v22310.
  rewrite ?node_8058.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22311 (s : N.State) (i : N.Inputs) :
  R.v22311 (state s) (inputs i) = Zmod.unsigned (N.v22311 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22311 s i)) at 1.
  unfold R.v22311, N.v22311.
  unfold R.v16463, N.v16463.
  rewrite !state_r651_nr_5F651.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r651_nr_5F651 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22312 (s : N.State) (i : N.Inputs) :
  R.v22312 (state s) (inputs i) = Zmod.unsigned (N.v22312 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22312 s i)) at 1.
  unfold R.v22312, N.v22312.
  unfold R.v16463, N.v16463.
  rewrite !state_r650_nr_5F650.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r650_nr_5F650 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22313 (s : N.State) (i : N.Inputs) :
  R.v22313 (state s) (inputs i) = Zmod.unsigned (N.v22313 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22313 s i)) at 1.
  unfold R.v22313, N.v22313.
  unfold R.v6, N.v6.
  rewrite !state_r649_nr_5F649.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r649_nr_5F649 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22314 (s : N.State) (i : N.Inputs) :
  R.v22314 (state s) (inputs i) = Zmod.unsigned (N.v22314 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22314 s i)) at 1.
  unfold R.v22314, N.v22314.
  unfold R.v6, N.v6.
  rewrite !state_r648_nr_5F648.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r648_nr_5F648 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22315 (s : N.State) (i : N.Inputs) :
  R.v22315 (state s) (inputs i) = Zmod.unsigned (N.v22315 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22315 s i)) at 1.
  unfold R.v22315, N.v22315.
  rewrite ?node_22313.
  rewrite ?node_22314.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22316 (s : N.State) (i : N.Inputs) :
  R.v22316 (state s) (inputs i) = Zmod.unsigned (N.v22316 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22316 s i)) at 1.
  unfold R.v22316, N.v22316.
  unfold R.v16484, N.v16484.
  rewrite ?node_22315.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22317 (s : N.State) (i : N.Inputs) :
  R.v22317 (state s) (inputs i) = Zmod.unsigned (N.v22317 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22317 s i)) at 1.
  unfold R.v22317, N.v22317.
  rewrite ?node_22310.
  rewrite ?node_22311.
  rewrite ?node_22312.
  rewrite ?node_22316.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22318 (s : N.State) (i : N.Inputs) :
  R.v22318 (state s) (inputs i) = Zmod.unsigned (N.v22318 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22318 s i)) at 1.
  unfold R.v22318, N.v22318.
  unfold R.v6, N.v6.
  rewrite ?node_22317.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22319 (s : N.State) (i : N.Inputs) :
  R.v22319 (state s) (inputs i) = Zmod.unsigned (N.v22319 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22319 s i)) at 1.
  unfold R.v22319, N.v22319.
  rewrite ?node_8059.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22320 (s : N.State) (i : N.Inputs) :
  R.v22320 (state s) (inputs i) = Zmod.unsigned (N.v22320 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22320 s i)) at 1.
  unfold R.v22320, N.v22320.
  unfold R.v6, N.v6.
  rewrite ?node_8178.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22321 (s : N.State) (i : N.Inputs) :
  R.v22321 (state s) (inputs i) = Zmod.unsigned (N.v22321 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22321 s i)) at 1.
  unfold R.v22321, N.v22321.
  unfold R.v6, N.v6.
  rewrite ?node_8227.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22322 (s : N.State) (i : N.Inputs) :
  R.v22322 (state s) (inputs i) = Zmod.unsigned (N.v22322 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22322 s i)) at 1.
  unfold R.v22322, N.v22322.
  rewrite ?node_22319.
  rewrite ?node_22320.
  rewrite ?node_22321.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22323 (s : N.State) (i : N.Inputs) :
  R.v22323 (state s) (inputs i) = Zmod.unsigned (N.v22323 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22323 s i)) at 1.
  unfold R.v22323, N.v22323.
  rewrite ?node_22318.
  rewrite ?node_22322.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22324 (s : N.State) (i : N.Inputs) :
  R.v22324 (state s) (inputs i) = Zmod.unsigned (N.v22324 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22324 s i)) at 1.
  unfold R.v22324, N.v22324.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22325 (s : N.State) (i : N.Inputs) :
  R.v22325 (state s) (inputs i) = Zmod.unsigned (N.v22325 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22325 s i)) at 1.
  unfold R.v22325, N.v22325.
  unfold R.v16463, N.v16463.
  rewrite !state_r650_nr_5F650.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r650_nr_5F650 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22326 (s : N.State) (i : N.Inputs) :
  R.v22326 (state s) (inputs i) = Zmod.unsigned (N.v22326 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22326 s i)) at 1.
  unfold R.v22326, N.v22326.
  unfold R.v6, N.v6.
  rewrite !state_r649_nr_5F649.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r649_nr_5F649 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22327 (s : N.State) (i : N.Inputs) :
  R.v22327 (state s) (inputs i) = Zmod.unsigned (N.v22327 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22327 s i)) at 1.
  unfold R.v22327, N.v22327.
  unfold R.v6, N.v6.
  rewrite !state_r648_nr_5F648.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r648_nr_5F648 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22328 (s : N.State) (i : N.Inputs) :
  R.v22328 (state s) (inputs i) = Zmod.unsigned (N.v22328 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22328 s i)) at 1.
  unfold R.v22328, N.v22328.
  rewrite ?node_22326.
  rewrite ?node_22327.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22329 (s : N.State) (i : N.Inputs) :
  R.v22329 (state s) (inputs i) = Zmod.unsigned (N.v22329 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22329 s i)) at 1.
  unfold R.v22329, N.v22329.
  unfold R.v16484, N.v16484.
  rewrite ?node_22328.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22330 (s : N.State) (i : N.Inputs) :
  R.v22330 (state s) (inputs i) = Zmod.unsigned (N.v22330 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22330 s i)) at 1.
  unfold R.v22330, N.v22330.
  rewrite ?node_22325.
  rewrite ?node_22329.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22331 (s : N.State) (i : N.Inputs) :
  R.v22331 (state s) (inputs i) = Zmod.unsigned (N.v22331 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22331 s i)) at 1.
  unfold R.v22331, N.v22331.
  unfold R.v6, N.v6.
  rewrite ?node_22330.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22332 (s : N.State) (i : N.Inputs) :
  R.v22332 (state s) (inputs i) = Zmod.unsigned (N.v22332 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22332 s i)) at 1.
  unfold R.v22332, N.v22332.
  rewrite ?node_8054.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22333 (s : N.State) (i : N.Inputs) :
  R.v22333 (state s) (inputs i) = Zmod.unsigned (N.v22333 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22333 s i)) at 1.
  unfold R.v22333, N.v22333.
  unfold R.v6, N.v6.
  rewrite ?node_8178.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22334 (s : N.State) (i : N.Inputs) :
  R.v22334 (state s) (inputs i) = Zmod.unsigned (N.v22334 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22334 s i)) at 1.
  unfold R.v22334, N.v22334.
  rewrite ?node_22332.
  rewrite ?node_22333.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22335 (s : N.State) (i : N.Inputs) :
  R.v22335 (state s) (inputs i) = Zmod.unsigned (N.v22335 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22335 s i)) at 1.
  unfold R.v22335, N.v22335.
  rewrite ?node_22331.
  rewrite ?node_22334.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22336 (s : N.State) (i : N.Inputs) :
  R.v22336 (state s) (inputs i) = Zmod.unsigned (N.v22336 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22336 s i)) at 1.
  unfold R.v22336, N.v22336.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22337 (s : N.State) (i : N.Inputs) :
  R.v22337 (state s) (inputs i) = Zmod.unsigned (N.v22337 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22337 s i)) at 1.
  unfold R.v22337, N.v22337.
  rewrite ?node_8058.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22338 (s : N.State) (i : N.Inputs) :
  R.v22338 (state s) (inputs i) = Zmod.unsigned (N.v22338 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22338 s i)) at 1.
  unfold R.v22338, N.v22338.
  unfold R.v6, N.v6.
  rewrite !state_r651_nr_5F651.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r651_nr_5F651 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22339 (s : N.State) (i : N.Inputs) :
  R.v22339 (state s) (inputs i) = Zmod.unsigned (N.v22339 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22339 s i)) at 1.
  unfold R.v22339, N.v22339.
  unfold R.v6, N.v6.
  rewrite ?node_8054.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22340 (s : N.State) (i : N.Inputs) :
  R.v22340 (state s) (inputs i) = Zmod.unsigned (N.v22340 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22340 s i)) at 1.
  unfold R.v22340, N.v22340.
  rewrite ?node_22338.
  rewrite ?node_22339.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22341 (s : N.State) (i : N.Inputs) :
  R.v22341 (state s) (inputs i) = Zmod.unsigned (N.v22341 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22341 s i)) at 1.
  unfold R.v22341, N.v22341.
  unfold R.v16484, N.v16484.
  rewrite ?node_22340.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22342 (s : N.State) (i : N.Inputs) :
  R.v22342 (state s) (inputs i) = Zmod.unsigned (N.v22342 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22342 s i)) at 1.
  unfold R.v22342, N.v22342.
  rewrite ?node_22337.
  rewrite ?node_22341.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22343 (s : N.State) (i : N.Inputs) :
  R.v22343 (state s) (inputs i) = Zmod.unsigned (N.v22343 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22343 s i)) at 1.
  unfold R.v22343, N.v22343.
  unfold R.v6, N.v6.
  rewrite ?node_22342.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22344 (s : N.State) (i : N.Inputs) :
  R.v22344 (state s) (inputs i) = Zmod.unsigned (N.v22344 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22344 s i)) at 1.
  unfold R.v22344, N.v22344.
  rewrite ?node_8059.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22345 (s : N.State) (i : N.Inputs) :
  R.v22345 (state s) (inputs i) = Zmod.unsigned (N.v22345 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22345 s i)) at 1.
  unfold R.v22345, N.v22345.
  unfold R.v6, N.v6.
  rewrite ?node_8227.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22346 (s : N.State) (i : N.Inputs) :
  R.v22346 (state s) (inputs i) = Zmod.unsigned (N.v22346 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22346 s i)) at 1.
  unfold R.v22346, N.v22346.
  rewrite ?node_22344.
  rewrite ?node_22345.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22347 (s : N.State) (i : N.Inputs) :
  R.v22347 (state s) (inputs i) = Zmod.unsigned (N.v22347 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22347 s i)) at 1.
  unfold R.v22347, N.v22347.
  rewrite ?node_22343.
  rewrite ?node_22346.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22348 (s : N.State) (i : N.Inputs) :
  R.v22348 (state s) (inputs i) = Zmod.unsigned (N.v22348 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22348 s i)) at 1.
  unfold R.v22348, N.v22348.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22349 (s : N.State) (i : N.Inputs) :
  R.v22349 (state s) (inputs i) = Zmod.unsigned (N.v22349 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22349 s i)) at 1.
  unfold R.v22349, N.v22349.
  rewrite ?node_8065.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22350 (s : N.State) (i : N.Inputs) :
  R.v22350 (state s) (inputs i) = Zmod.unsigned (N.v22350 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22350 s i)) at 1.
  unfold R.v22350, N.v22350.
  unfold R.v16463, N.v16463.
  rewrite !state_r655_nr_5F655.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r655_nr_5F655 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22351 (s : N.State) (i : N.Inputs) :
  R.v22351 (state s) (inputs i) = Zmod.unsigned (N.v22351 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22351 s i)) at 1.
  unfold R.v22351, N.v22351.
  unfold R.v16463, N.v16463.
  rewrite !state_r654_nr_5F654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r654_nr_5F654 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22352 (s : N.State) (i : N.Inputs) :
  R.v22352 (state s) (inputs i) = Zmod.unsigned (N.v22352 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22352 s i)) at 1.
  unfold R.v22352, N.v22352.
  unfold R.v6, N.v6.
  rewrite !state_r653_nr_5F653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r653_nr_5F653 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22353 (s : N.State) (i : N.Inputs) :
  R.v22353 (state s) (inputs i) = Zmod.unsigned (N.v22353 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22353 s i)) at 1.
  unfold R.v22353, N.v22353.
  unfold R.v6, N.v6.
  rewrite !state_r652_nr_5F652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r652_nr_5F652 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22354 (s : N.State) (i : N.Inputs) :
  R.v22354 (state s) (inputs i) = Zmod.unsigned (N.v22354 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22354 s i)) at 1.
  unfold R.v22354, N.v22354.
  rewrite ?node_22352.
  rewrite ?node_22353.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22355 (s : N.State) (i : N.Inputs) :
  R.v22355 (state s) (inputs i) = Zmod.unsigned (N.v22355 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22355 s i)) at 1.
  unfold R.v22355, N.v22355.
  unfold R.v16484, N.v16484.
  rewrite ?node_22354.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22356 (s : N.State) (i : N.Inputs) :
  R.v22356 (state s) (inputs i) = Zmod.unsigned (N.v22356 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22356 s i)) at 1.
  unfold R.v22356, N.v22356.
  rewrite ?node_22349.
  rewrite ?node_22350.
  rewrite ?node_22351.
  rewrite ?node_22355.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22357 (s : N.State) (i : N.Inputs) :
  R.v22357 (state s) (inputs i) = Zmod.unsigned (N.v22357 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22357 s i)) at 1.
  unfold R.v22357, N.v22357.
  unfold R.v6, N.v6.
  rewrite ?node_22356.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22358 (s : N.State) (i : N.Inputs) :
  R.v22358 (state s) (inputs i) = Zmod.unsigned (N.v22358 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22358 s i)) at 1.
  unfold R.v22358, N.v22358.
  rewrite ?node_8066.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22359 (s : N.State) (i : N.Inputs) :
  R.v22359 (state s) (inputs i) = Zmod.unsigned (N.v22359 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22359 s i)) at 1.
  unfold R.v22359, N.v22359.
  unfold R.v6, N.v6.
  rewrite ?node_8185.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22360 (s : N.State) (i : N.Inputs) :
  R.v22360 (state s) (inputs i) = Zmod.unsigned (N.v22360 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22360 s i)) at 1.
  unfold R.v22360, N.v22360.
  unfold R.v6, N.v6.
  rewrite ?node_8236.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22361 (s : N.State) (i : N.Inputs) :
  R.v22361 (state s) (inputs i) = Zmod.unsigned (N.v22361 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22361 s i)) at 1.
  unfold R.v22361, N.v22361.
  rewrite ?node_22358.
  rewrite ?node_22359.
  rewrite ?node_22360.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22362 (s : N.State) (i : N.Inputs) :
  R.v22362 (state s) (inputs i) = Zmod.unsigned (N.v22362 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22362 s i)) at 1.
  unfold R.v22362, N.v22362.
  rewrite ?node_22357.
  rewrite ?node_22361.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22363 (s : N.State) (i : N.Inputs) :
  R.v22363 (state s) (inputs i) = Zmod.unsigned (N.v22363 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22363 s i)) at 1.
  unfold R.v22363, N.v22363.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22364 (s : N.State) (i : N.Inputs) :
  R.v22364 (state s) (inputs i) = Zmod.unsigned (N.v22364 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22364 s i)) at 1.
  unfold R.v22364, N.v22364.
  unfold R.v16463, N.v16463.
  rewrite !state_r654_nr_5F654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r654_nr_5F654 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22365 (s : N.State) (i : N.Inputs) :
  R.v22365 (state s) (inputs i) = Zmod.unsigned (N.v22365 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22365 s i)) at 1.
  unfold R.v22365, N.v22365.
  unfold R.v6, N.v6.
  rewrite !state_r653_nr_5F653.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r653_nr_5F653 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22366 (s : N.State) (i : N.Inputs) :
  R.v22366 (state s) (inputs i) = Zmod.unsigned (N.v22366 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22366 s i)) at 1.
  unfold R.v22366, N.v22366.
  unfold R.v6, N.v6.
  rewrite !state_r652_nr_5F652.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r652_nr_5F652 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22367 (s : N.State) (i : N.Inputs) :
  R.v22367 (state s) (inputs i) = Zmod.unsigned (N.v22367 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22367 s i)) at 1.
  unfold R.v22367, N.v22367.
  rewrite ?node_22365.
  rewrite ?node_22366.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22368 (s : N.State) (i : N.Inputs) :
  R.v22368 (state s) (inputs i) = Zmod.unsigned (N.v22368 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22368 s i)) at 1.
  unfold R.v22368, N.v22368.
  unfold R.v16484, N.v16484.
  rewrite ?node_22367.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22369 (s : N.State) (i : N.Inputs) :
  R.v22369 (state s) (inputs i) = Zmod.unsigned (N.v22369 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22369 s i)) at 1.
  unfold R.v22369, N.v22369.
  rewrite ?node_22364.
  rewrite ?node_22368.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22370 (s : N.State) (i : N.Inputs) :
  R.v22370 (state s) (inputs i) = Zmod.unsigned (N.v22370 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22370 s i)) at 1.
  unfold R.v22370, N.v22370.
  unfold R.v6, N.v6.
  rewrite ?node_22369.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22371 (s : N.State) (i : N.Inputs) :
  R.v22371 (state s) (inputs i) = Zmod.unsigned (N.v22371 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22371 s i)) at 1.
  unfold R.v22371, N.v22371.
  rewrite ?node_8061.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22372 (s : N.State) (i : N.Inputs) :
  R.v22372 (state s) (inputs i) = Zmod.unsigned (N.v22372 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22372 s i)) at 1.
  unfold R.v22372, N.v22372.
  unfold R.v6, N.v6.
  rewrite ?node_8185.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22373 (s : N.State) (i : N.Inputs) :
  R.v22373 (state s) (inputs i) = Zmod.unsigned (N.v22373 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22373 s i)) at 1.
  unfold R.v22373, N.v22373.
  rewrite ?node_22371.
  rewrite ?node_22372.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22374 (s : N.State) (i : N.Inputs) :
  R.v22374 (state s) (inputs i) = Zmod.unsigned (N.v22374 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22374 s i)) at 1.
  unfold R.v22374, N.v22374.
  rewrite ?node_22370.
  rewrite ?node_22373.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22375 (s : N.State) (i : N.Inputs) :
  R.v22375 (state s) (inputs i) = Zmod.unsigned (N.v22375 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22375 s i)) at 1.
  unfold R.v22375, N.v22375.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22376 (s : N.State) (i : N.Inputs) :
  R.v22376 (state s) (inputs i) = Zmod.unsigned (N.v22376 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22376 s i)) at 1.
  unfold R.v22376, N.v22376.
  rewrite ?node_8065.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22377 (s : N.State) (i : N.Inputs) :
  R.v22377 (state s) (inputs i) = Zmod.unsigned (N.v22377 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22377 s i)) at 1.
  unfold R.v22377, N.v22377.
  unfold R.v6, N.v6.
  rewrite !state_r655_nr_5F655.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r655_nr_5F655 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22378 (s : N.State) (i : N.Inputs) :
  R.v22378 (state s) (inputs i) = Zmod.unsigned (N.v22378 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22378 s i)) at 1.
  unfold R.v22378, N.v22378.
  unfold R.v6, N.v6.
  rewrite ?node_8061.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22379 (s : N.State) (i : N.Inputs) :
  R.v22379 (state s) (inputs i) = Zmod.unsigned (N.v22379 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22379 s i)) at 1.
  unfold R.v22379, N.v22379.
  rewrite ?node_22377.
  rewrite ?node_22378.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22380 (s : N.State) (i : N.Inputs) :
  R.v22380 (state s) (inputs i) = Zmod.unsigned (N.v22380 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22380 s i)) at 1.
  unfold R.v22380, N.v22380.
  unfold R.v16484, N.v16484.
  rewrite ?node_22379.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22381 (s : N.State) (i : N.Inputs) :
  R.v22381 (state s) (inputs i) = Zmod.unsigned (N.v22381 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22381 s i)) at 1.
  unfold R.v22381, N.v22381.
  rewrite ?node_22376.
  rewrite ?node_22380.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22382 (s : N.State) (i : N.Inputs) :
  R.v22382 (state s) (inputs i) = Zmod.unsigned (N.v22382 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22382 s i)) at 1.
  unfold R.v22382, N.v22382.
  unfold R.v6, N.v6.
  rewrite ?node_22381.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22383 (s : N.State) (i : N.Inputs) :
  R.v22383 (state s) (inputs i) = Zmod.unsigned (N.v22383 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22383 s i)) at 1.
  unfold R.v22383, N.v22383.
  rewrite ?node_8066.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22384 (s : N.State) (i : N.Inputs) :
  R.v22384 (state s) (inputs i) = Zmod.unsigned (N.v22384 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22384 s i)) at 1.
  unfold R.v22384, N.v22384.
  unfold R.v6, N.v6.
  rewrite ?node_8236.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22385 (s : N.State) (i : N.Inputs) :
  R.v22385 (state s) (inputs i) = Zmod.unsigned (N.v22385 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22385 s i)) at 1.
  unfold R.v22385, N.v22385.
  rewrite ?node_22383.
  rewrite ?node_22384.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22386 (s : N.State) (i : N.Inputs) :
  R.v22386 (state s) (inputs i) = Zmod.unsigned (N.v22386 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22386 s i)) at 1.
  unfold R.v22386, N.v22386.
  rewrite ?node_22382.
  rewrite ?node_22385.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22387 (s : N.State) (i : N.Inputs) :
  R.v22387 (state s) (inputs i) = Zmod.unsigned (N.v22387 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22387 s i)) at 1.
  unfold R.v22387, N.v22387.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22388 (s : N.State) (i : N.Inputs) :
  R.v22388 (state s) (inputs i) = Zmod.unsigned (N.v22388 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22388 s i)) at 1.
  unfold R.v22388, N.v22388.
  rewrite ?node_8073.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22389 (s : N.State) (i : N.Inputs) :
  R.v22389 (state s) (inputs i) = Zmod.unsigned (N.v22389 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22389 s i)) at 1.
  unfold R.v22389, N.v22389.
  unfold R.v16463, N.v16463.
  rewrite !state_r659_nr_5F659.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r659_nr_5F659 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22390 (s : N.State) (i : N.Inputs) :
  R.v22390 (state s) (inputs i) = Zmod.unsigned (N.v22390 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22390 s i)) at 1.
  unfold R.v22390, N.v22390.
  unfold R.v16463, N.v16463.
  rewrite !state_r658_nr_5F658.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r658_nr_5F658 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22391 (s : N.State) (i : N.Inputs) :
  R.v22391 (state s) (inputs i) = Zmod.unsigned (N.v22391 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22391 s i)) at 1.
  unfold R.v22391, N.v22391.
  unfold R.v6, N.v6.
  rewrite !state_r657_nr_5F657.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r657_nr_5F657 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22392 (s : N.State) (i : N.Inputs) :
  R.v22392 (state s) (inputs i) = Zmod.unsigned (N.v22392 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22392 s i)) at 1.
  unfold R.v22392, N.v22392.
  unfold R.v6, N.v6.
  rewrite !state_r656_nr_5F656.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r656_nr_5F656 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22393 (s : N.State) (i : N.Inputs) :
  R.v22393 (state s) (inputs i) = Zmod.unsigned (N.v22393 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22393 s i)) at 1.
  unfold R.v22393, N.v22393.
  rewrite ?node_22391.
  rewrite ?node_22392.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22394 (s : N.State) (i : N.Inputs) :
  R.v22394 (state s) (inputs i) = Zmod.unsigned (N.v22394 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22394 s i)) at 1.
  unfold R.v22394, N.v22394.
  unfold R.v16484, N.v16484.
  rewrite ?node_22393.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22395 (s : N.State) (i : N.Inputs) :
  R.v22395 (state s) (inputs i) = Zmod.unsigned (N.v22395 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22395 s i)) at 1.
  unfold R.v22395, N.v22395.
  rewrite ?node_22388.
  rewrite ?node_22389.
  rewrite ?node_22390.
  rewrite ?node_22394.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22396 (s : N.State) (i : N.Inputs) :
  R.v22396 (state s) (inputs i) = Zmod.unsigned (N.v22396 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22396 s i)) at 1.
  unfold R.v22396, N.v22396.
  unfold R.v6, N.v6.
  rewrite ?node_22395.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22397 (s : N.State) (i : N.Inputs) :
  R.v22397 (state s) (inputs i) = Zmod.unsigned (N.v22397 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22397 s i)) at 1.
  unfold R.v22397, N.v22397.
  rewrite ?node_8074.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22398 (s : N.State) (i : N.Inputs) :
  R.v22398 (state s) (inputs i) = Zmod.unsigned (N.v22398 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22398 s i)) at 1.
  unfold R.v22398, N.v22398.
  unfold R.v6, N.v6.
  rewrite ?node_8193.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22399 (s : N.State) (i : N.Inputs) :
  R.v22399 (state s) (inputs i) = Zmod.unsigned (N.v22399 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22399 s i)) at 1.
  unfold R.v22399, N.v22399.
  unfold R.v6, N.v6.
  rewrite ?node_8239.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22400 (s : N.State) (i : N.Inputs) :
  R.v22400 (state s) (inputs i) = Zmod.unsigned (N.v22400 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22400 s i)) at 1.
  unfold R.v22400, N.v22400.
  rewrite ?node_22397.
  rewrite ?node_22398.
  rewrite ?node_22399.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22401 (s : N.State) (i : N.Inputs) :
  R.v22401 (state s) (inputs i) = Zmod.unsigned (N.v22401 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22401 s i)) at 1.
  unfold R.v22401, N.v22401.
  rewrite ?node_22396.
  rewrite ?node_22400.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22402 (s : N.State) (i : N.Inputs) :
  R.v22402 (state s) (inputs i) = Zmod.unsigned (N.v22402 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22402 s i)) at 1.
  unfold R.v22402, N.v22402.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22403 (s : N.State) (i : N.Inputs) :
  R.v22403 (state s) (inputs i) = Zmod.unsigned (N.v22403 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22403 s i)) at 1.
  unfold R.v22403, N.v22403.
  unfold R.v16463, N.v16463.
  rewrite !state_r658_nr_5F658.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r658_nr_5F658 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22404 (s : N.State) (i : N.Inputs) :
  R.v22404 (state s) (inputs i) = Zmod.unsigned (N.v22404 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22404 s i)) at 1.
  unfold R.v22404, N.v22404.
  unfold R.v6, N.v6.
  rewrite !state_r657_nr_5F657.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r657_nr_5F657 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22405 (s : N.State) (i : N.Inputs) :
  R.v22405 (state s) (inputs i) = Zmod.unsigned (N.v22405 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22405 s i)) at 1.
  unfold R.v22405, N.v22405.
  unfold R.v6, N.v6.
  rewrite !state_r656_nr_5F656.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r656_nr_5F656 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22406 (s : N.State) (i : N.Inputs) :
  R.v22406 (state s) (inputs i) = Zmod.unsigned (N.v22406 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22406 s i)) at 1.
  unfold R.v22406, N.v22406.
  rewrite ?node_22404.
  rewrite ?node_22405.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22407 (s : N.State) (i : N.Inputs) :
  R.v22407 (state s) (inputs i) = Zmod.unsigned (N.v22407 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22407 s i)) at 1.
  unfold R.v22407, N.v22407.
  unfold R.v16484, N.v16484.
  rewrite ?node_22406.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22408 (s : N.State) (i : N.Inputs) :
  R.v22408 (state s) (inputs i) = Zmod.unsigned (N.v22408 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22408 s i)) at 1.
  unfold R.v22408, N.v22408.
  rewrite ?node_22403.
  rewrite ?node_22407.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22409 (s : N.State) (i : N.Inputs) :
  R.v22409 (state s) (inputs i) = Zmod.unsigned (N.v22409 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22409 s i)) at 1.
  unfold R.v22409, N.v22409.
  unfold R.v6, N.v6.
  rewrite ?node_22408.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22410 (s : N.State) (i : N.Inputs) :
  R.v22410 (state s) (inputs i) = Zmod.unsigned (N.v22410 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22410 s i)) at 1.
  unfold R.v22410, N.v22410.
  rewrite ?node_8069.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22411 (s : N.State) (i : N.Inputs) :
  R.v22411 (state s) (inputs i) = Zmod.unsigned (N.v22411 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22411 s i)) at 1.
  unfold R.v22411, N.v22411.
  unfold R.v6, N.v6.
  rewrite ?node_8193.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22412 (s : N.State) (i : N.Inputs) :
  R.v22412 (state s) (inputs i) = Zmod.unsigned (N.v22412 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22412 s i)) at 1.
  unfold R.v22412, N.v22412.
  rewrite ?node_22410.
  rewrite ?node_22411.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22413 (s : N.State) (i : N.Inputs) :
  R.v22413 (state s) (inputs i) = Zmod.unsigned (N.v22413 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22413 s i)) at 1.
  unfold R.v22413, N.v22413.
  rewrite ?node_22409.
  rewrite ?node_22412.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22414 (s : N.State) (i : N.Inputs) :
  R.v22414 (state s) (inputs i) = Zmod.unsigned (N.v22414 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22414 s i)) at 1.
  unfold R.v22414, N.v22414.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22415 (s : N.State) (i : N.Inputs) :
  R.v22415 (state s) (inputs i) = Zmod.unsigned (N.v22415 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22415 s i)) at 1.
  unfold R.v22415, N.v22415.
  rewrite ?node_8073.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22416 (s : N.State) (i : N.Inputs) :
  R.v22416 (state s) (inputs i) = Zmod.unsigned (N.v22416 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22416 s i)) at 1.
  unfold R.v22416, N.v22416.
  unfold R.v6, N.v6.
  rewrite !state_r659_nr_5F659.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r659_nr_5F659 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22417 (s : N.State) (i : N.Inputs) :
  R.v22417 (state s) (inputs i) = Zmod.unsigned (N.v22417 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22417 s i)) at 1.
  unfold R.v22417, N.v22417.
  unfold R.v6, N.v6.
  rewrite ?node_8069.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22418 (s : N.State) (i : N.Inputs) :
  R.v22418 (state s) (inputs i) = Zmod.unsigned (N.v22418 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22418 s i)) at 1.
  unfold R.v22418, N.v22418.
  rewrite ?node_22416.
  rewrite ?node_22417.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22419 (s : N.State) (i : N.Inputs) :
  R.v22419 (state s) (inputs i) = Zmod.unsigned (N.v22419 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22419 s i)) at 1.
  unfold R.v22419, N.v22419.
  unfold R.v16484, N.v16484.
  rewrite ?node_22418.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22420 (s : N.State) (i : N.Inputs) :
  R.v22420 (state s) (inputs i) = Zmod.unsigned (N.v22420 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22420 s i)) at 1.
  unfold R.v22420, N.v22420.
  rewrite ?node_22415.
  rewrite ?node_22419.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22421 (s : N.State) (i : N.Inputs) :
  R.v22421 (state s) (inputs i) = Zmod.unsigned (N.v22421 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22421 s i)) at 1.
  unfold R.v22421, N.v22421.
  unfold R.v6, N.v6.
  rewrite ?node_22420.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22422 (s : N.State) (i : N.Inputs) :
  R.v22422 (state s) (inputs i) = Zmod.unsigned (N.v22422 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22422 s i)) at 1.
  unfold R.v22422, N.v22422.
  rewrite ?node_8074.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22423 (s : N.State) (i : N.Inputs) :
  R.v22423 (state s) (inputs i) = Zmod.unsigned (N.v22423 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22423 s i)) at 1.
  unfold R.v22423, N.v22423.
  unfold R.v6, N.v6.
  rewrite ?node_8239.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22424 (s : N.State) (i : N.Inputs) :
  R.v22424 (state s) (inputs i) = Zmod.unsigned (N.v22424 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22424 s i)) at 1.
  unfold R.v22424, N.v22424.
  rewrite ?node_22422.
  rewrite ?node_22423.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22425 (s : N.State) (i : N.Inputs) :
  R.v22425 (state s) (inputs i) = Zmod.unsigned (N.v22425 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22425 s i)) at 1.
  unfold R.v22425, N.v22425.
  rewrite ?node_22421.
  rewrite ?node_22424.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22426 (s : N.State) (i : N.Inputs) :
  R.v22426 (state s) (inputs i) = Zmod.unsigned (N.v22426 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22426 s i)) at 1.
  unfold R.v22426, N.v22426.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22427 (s : N.State) (i : N.Inputs) :
  R.v22427 (state s) (inputs i) = Zmod.unsigned (N.v22427 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22427 s i)) at 1.
  unfold R.v22427, N.v22427.
  rewrite ?node_8081.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22428 (s : N.State) (i : N.Inputs) :
  R.v22428 (state s) (inputs i) = Zmod.unsigned (N.v22428 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22428 s i)) at 1.
  unfold R.v22428, N.v22428.
  unfold R.v16463, N.v16463.
  rewrite !state_r663_nr_5F663.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r663_nr_5F663 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22429 (s : N.State) (i : N.Inputs) :
  R.v22429 (state s) (inputs i) = Zmod.unsigned (N.v22429 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22429 s i)) at 1.
  unfold R.v22429, N.v22429.
  unfold R.v16463, N.v16463.
  rewrite !state_r662_nr_5F662.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r662_nr_5F662 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22430 (s : N.State) (i : N.Inputs) :
  R.v22430 (state s) (inputs i) = Zmod.unsigned (N.v22430 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22430 s i)) at 1.
  unfold R.v22430, N.v22430.
  unfold R.v6, N.v6.
  rewrite !state_r661_nr_5F661.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r661_nr_5F661 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22431 (s : N.State) (i : N.Inputs) :
  R.v22431 (state s) (inputs i) = Zmod.unsigned (N.v22431 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22431 s i)) at 1.
  unfold R.v22431, N.v22431.
  unfold R.v6, N.v6.
  rewrite !state_r660_nr_5F660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r660_nr_5F660 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22432 (s : N.State) (i : N.Inputs) :
  R.v22432 (state s) (inputs i) = Zmod.unsigned (N.v22432 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22432 s i)) at 1.
  unfold R.v22432, N.v22432.
  rewrite ?node_22430.
  rewrite ?node_22431.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22433 (s : N.State) (i : N.Inputs) :
  R.v22433 (state s) (inputs i) = Zmod.unsigned (N.v22433 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22433 s i)) at 1.
  unfold R.v22433, N.v22433.
  unfold R.v16484, N.v16484.
  rewrite ?node_22432.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22434 (s : N.State) (i : N.Inputs) :
  R.v22434 (state s) (inputs i) = Zmod.unsigned (N.v22434 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22434 s i)) at 1.
  unfold R.v22434, N.v22434.
  rewrite ?node_22427.
  rewrite ?node_22428.
  rewrite ?node_22429.
  rewrite ?node_22433.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22435 (s : N.State) (i : N.Inputs) :
  R.v22435 (state s) (inputs i) = Zmod.unsigned (N.v22435 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22435 s i)) at 1.
  unfold R.v22435, N.v22435.
  unfold R.v6, N.v6.
  rewrite ?node_22434.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22436 (s : N.State) (i : N.Inputs) :
  R.v22436 (state s) (inputs i) = Zmod.unsigned (N.v22436 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22436 s i)) at 1.
  unfold R.v22436, N.v22436.
  rewrite ?node_8082.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22437 (s : N.State) (i : N.Inputs) :
  R.v22437 (state s) (inputs i) = Zmod.unsigned (N.v22437 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22437 s i)) at 1.
  unfold R.v22437, N.v22437.
  unfold R.v6, N.v6.
  rewrite ?node_8201.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22438 (s : N.State) (i : N.Inputs) :
  R.v22438 (state s) (inputs i) = Zmod.unsigned (N.v22438 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22438 s i)) at 1.
  unfold R.v22438, N.v22438.
  unfold R.v6, N.v6.
  rewrite ?node_8243.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22439 (s : N.State) (i : N.Inputs) :
  R.v22439 (state s) (inputs i) = Zmod.unsigned (N.v22439 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22439 s i)) at 1.
  unfold R.v22439, N.v22439.
  rewrite ?node_22436.
  rewrite ?node_22437.
  rewrite ?node_22438.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22440 (s : N.State) (i : N.Inputs) :
  R.v22440 (state s) (inputs i) = Zmod.unsigned (N.v22440 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22440 s i)) at 1.
  unfold R.v22440, N.v22440.
  rewrite ?node_22435.
  rewrite ?node_22439.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22441 (s : N.State) (i : N.Inputs) :
  R.v22441 (state s) (inputs i) = Zmod.unsigned (N.v22441 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22441 s i)) at 1.
  unfold R.v22441, N.v22441.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22442 (s : N.State) (i : N.Inputs) :
  R.v22442 (state s) (inputs i) = Zmod.unsigned (N.v22442 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22442 s i)) at 1.
  unfold R.v22442, N.v22442.
  unfold R.v16463, N.v16463.
  rewrite !state_r662_nr_5F662.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r662_nr_5F662 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22443 (s : N.State) (i : N.Inputs) :
  R.v22443 (state s) (inputs i) = Zmod.unsigned (N.v22443 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22443 s i)) at 1.
  unfold R.v22443, N.v22443.
  unfold R.v6, N.v6.
  rewrite !state_r661_nr_5F661.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r661_nr_5F661 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22444 (s : N.State) (i : N.Inputs) :
  R.v22444 (state s) (inputs i) = Zmod.unsigned (N.v22444 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22444 s i)) at 1.
  unfold R.v22444, N.v22444.
  unfold R.v6, N.v6.
  rewrite !state_r660_nr_5F660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r660_nr_5F660 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22445 (s : N.State) (i : N.Inputs) :
  R.v22445 (state s) (inputs i) = Zmod.unsigned (N.v22445 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22445 s i)) at 1.
  unfold R.v22445, N.v22445.
  rewrite ?node_22443.
  rewrite ?node_22444.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22446 (s : N.State) (i : N.Inputs) :
  R.v22446 (state s) (inputs i) = Zmod.unsigned (N.v22446 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22446 s i)) at 1.
  unfold R.v22446, N.v22446.
  unfold R.v16484, N.v16484.
  rewrite ?node_22445.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22447 (s : N.State) (i : N.Inputs) :
  R.v22447 (state s) (inputs i) = Zmod.unsigned (N.v22447 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22447 s i)) at 1.
  unfold R.v22447, N.v22447.
  rewrite ?node_22442.
  rewrite ?node_22446.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22448 (s : N.State) (i : N.Inputs) :
  R.v22448 (state s) (inputs i) = Zmod.unsigned (N.v22448 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22448 s i)) at 1.
  unfold R.v22448, N.v22448.
  unfold R.v6, N.v6.
  rewrite ?node_22447.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22449 (s : N.State) (i : N.Inputs) :
  R.v22449 (state s) (inputs i) = Zmod.unsigned (N.v22449 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22449 s i)) at 1.
  unfold R.v22449, N.v22449.
  rewrite ?node_8077.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22450 (s : N.State) (i : N.Inputs) :
  R.v22450 (state s) (inputs i) = Zmod.unsigned (N.v22450 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22450 s i)) at 1.
  unfold R.v22450, N.v22450.
  unfold R.v6, N.v6.
  rewrite ?node_8201.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22451 (s : N.State) (i : N.Inputs) :
  R.v22451 (state s) (inputs i) = Zmod.unsigned (N.v22451 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22451 s i)) at 1.
  unfold R.v22451, N.v22451.
  rewrite ?node_22449.
  rewrite ?node_22450.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22452 (s : N.State) (i : N.Inputs) :
  R.v22452 (state s) (inputs i) = Zmod.unsigned (N.v22452 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22452 s i)) at 1.
  unfold R.v22452, N.v22452.
  rewrite ?node_22448.
  rewrite ?node_22451.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22453 (s : N.State) (i : N.Inputs) :
  R.v22453 (state s) (inputs i) = Zmod.unsigned (N.v22453 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22453 s i)) at 1.
  unfold R.v22453, N.v22453.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22454 (s : N.State) (i : N.Inputs) :
  R.v22454 (state s) (inputs i) = Zmod.unsigned (N.v22454 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22454 s i)) at 1.
  unfold R.v22454, N.v22454.
  rewrite ?node_8081.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22455 (s : N.State) (i : N.Inputs) :
  R.v22455 (state s) (inputs i) = Zmod.unsigned (N.v22455 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22455 s i)) at 1.
  unfold R.v22455, N.v22455.
  unfold R.v6, N.v6.
  rewrite !state_r663_nr_5F663.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r663_nr_5F663 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22456 (s : N.State) (i : N.Inputs) :
  R.v22456 (state s) (inputs i) = Zmod.unsigned (N.v22456 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22456 s i)) at 1.
  unfold R.v22456, N.v22456.
  unfold R.v6, N.v6.
  rewrite ?node_8077.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22457 (s : N.State) (i : N.Inputs) :
  R.v22457 (state s) (inputs i) = Zmod.unsigned (N.v22457 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22457 s i)) at 1.
  unfold R.v22457, N.v22457.
  rewrite ?node_22455.
  rewrite ?node_22456.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22458 (s : N.State) (i : N.Inputs) :
  R.v22458 (state s) (inputs i) = Zmod.unsigned (N.v22458 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22458 s i)) at 1.
  unfold R.v22458, N.v22458.
  unfold R.v16484, N.v16484.
  rewrite ?node_22457.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22459 (s : N.State) (i : N.Inputs) :
  R.v22459 (state s) (inputs i) = Zmod.unsigned (N.v22459 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22459 s i)) at 1.
  unfold R.v22459, N.v22459.
  rewrite ?node_22454.
  rewrite ?node_22458.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22460 (s : N.State) (i : N.Inputs) :
  R.v22460 (state s) (inputs i) = Zmod.unsigned (N.v22460 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22460 s i)) at 1.
  unfold R.v22460, N.v22460.
  unfold R.v6, N.v6.
  rewrite ?node_22459.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22461 (s : N.State) (i : N.Inputs) :
  R.v22461 (state s) (inputs i) = Zmod.unsigned (N.v22461 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22461 s i)) at 1.
  unfold R.v22461, N.v22461.
  rewrite ?node_8082.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22462 (s : N.State) (i : N.Inputs) :
  R.v22462 (state s) (inputs i) = Zmod.unsigned (N.v22462 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22462 s i)) at 1.
  unfold R.v22462, N.v22462.
  unfold R.v6, N.v6.
  rewrite ?node_8243.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22463 (s : N.State) (i : N.Inputs) :
  R.v22463 (state s) (inputs i) = Zmod.unsigned (N.v22463 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22463 s i)) at 1.
  unfold R.v22463, N.v22463.
  rewrite ?node_22461.
  rewrite ?node_22462.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22464 (s : N.State) (i : N.Inputs) :
  R.v22464 (state s) (inputs i) = Zmod.unsigned (N.v22464 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22464 s i)) at 1.
  unfold R.v22464, N.v22464.
  rewrite ?node_22460.
  rewrite ?node_22463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22465 (s : N.State) (i : N.Inputs) :
  R.v22465 (state s) (inputs i) = Zmod.unsigned (N.v22465 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22465 s i)) at 1.
  unfold R.v22465, N.v22465.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22466 (s : N.State) (i : N.Inputs) :
  R.v22466 (state s) (inputs i) = Zmod.unsigned (N.v22466 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22466 s i)) at 1.
  unfold R.v22466, N.v22466.
  rewrite ?node_8093.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22467 (s : N.State) (i : N.Inputs) :
  R.v22467 (state s) (inputs i) = Zmod.unsigned (N.v22467 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22467 s i)) at 1.
  unfold R.v22467, N.v22467.
  unfold R.v16463, N.v16463.
  rewrite !state_r667_nr_5F667.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r667_nr_5F667 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22468 (s : N.State) (i : N.Inputs) :
  R.v22468 (state s) (inputs i) = Zmod.unsigned (N.v22468 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22468 s i)) at 1.
  unfold R.v22468, N.v22468.
  unfold R.v16463, N.v16463.
  rewrite !state_r666_nr_5F666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r666_nr_5F666 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22469 (s : N.State) (i : N.Inputs) :
  R.v22469 (state s) (inputs i) = Zmod.unsigned (N.v22469 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22469 s i)) at 1.
  unfold R.v22469, N.v22469.
  unfold R.v6, N.v6.
  rewrite !state_r665_nr_5F665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r665_nr_5F665 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22470 (s : N.State) (i : N.Inputs) :
  R.v22470 (state s) (inputs i) = Zmod.unsigned (N.v22470 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22470 s i)) at 1.
  unfold R.v22470, N.v22470.
  unfold R.v6, N.v6.
  rewrite !state_r664_nr_5F664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r664_nr_5F664 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22471 (s : N.State) (i : N.Inputs) :
  R.v22471 (state s) (inputs i) = Zmod.unsigned (N.v22471 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22471 s i)) at 1.
  unfold R.v22471, N.v22471.
  rewrite ?node_22469.
  rewrite ?node_22470.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22472 (s : N.State) (i : N.Inputs) :
  R.v22472 (state s) (inputs i) = Zmod.unsigned (N.v22472 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22472 s i)) at 1.
  unfold R.v22472, N.v22472.
  unfold R.v16484, N.v16484.
  rewrite ?node_22471.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22473 (s : N.State) (i : N.Inputs) :
  R.v22473 (state s) (inputs i) = Zmod.unsigned (N.v22473 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22473 s i)) at 1.
  unfold R.v22473, N.v22473.
  rewrite ?node_22466.
  rewrite ?node_22467.
  rewrite ?node_22468.
  rewrite ?node_22472.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22474 (s : N.State) (i : N.Inputs) :
  R.v22474 (state s) (inputs i) = Zmod.unsigned (N.v22474 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22474 s i)) at 1.
  unfold R.v22474, N.v22474.
  unfold R.v6, N.v6.
  rewrite ?node_22473.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22475 (s : N.State) (i : N.Inputs) :
  R.v22475 (state s) (inputs i) = Zmod.unsigned (N.v22475 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22475 s i)) at 1.
  unfold R.v22475, N.v22475.
  rewrite ?node_8094.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22476 (s : N.State) (i : N.Inputs) :
  R.v22476 (state s) (inputs i) = Zmod.unsigned (N.v22476 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22476 s i)) at 1.
  unfold R.v22476, N.v22476.
  unfold R.v6, N.v6.
  rewrite ?node_8213.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22477 (s : N.State) (i : N.Inputs) :
  R.v22477 (state s) (inputs i) = Zmod.unsigned (N.v22477 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22477 s i)) at 1.
  unfold R.v22477, N.v22477.
  unfold R.v6, N.v6.
  rewrite ?node_8247.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22478 (s : N.State) (i : N.Inputs) :
  R.v22478 (state s) (inputs i) = Zmod.unsigned (N.v22478 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22478 s i)) at 1.
  unfold R.v22478, N.v22478.
  rewrite ?node_22475.
  rewrite ?node_22476.
  rewrite ?node_22477.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22479 (s : N.State) (i : N.Inputs) :
  R.v22479 (state s) (inputs i) = Zmod.unsigned (N.v22479 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22479 s i)) at 1.
  unfold R.v22479, N.v22479.
  rewrite ?node_22474.
  rewrite ?node_22478.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22480 (s : N.State) (i : N.Inputs) :
  R.v22480 (state s) (inputs i) = Zmod.unsigned (N.v22480 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22480 s i)) at 1.
  unfold R.v22480, N.v22480.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22481 (s : N.State) (i : N.Inputs) :
  R.v22481 (state s) (inputs i) = Zmod.unsigned (N.v22481 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22481 s i)) at 1.
  unfold R.v22481, N.v22481.
  unfold R.v16463, N.v16463.
  rewrite !state_r666_nr_5F666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r666_nr_5F666 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22482 (s : N.State) (i : N.Inputs) :
  R.v22482 (state s) (inputs i) = Zmod.unsigned (N.v22482 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22482 s i)) at 1.
  unfold R.v22482, N.v22482.
  unfold R.v6, N.v6.
  rewrite !state_r665_nr_5F665.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r665_nr_5F665 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22483 (s : N.State) (i : N.Inputs) :
  R.v22483 (state s) (inputs i) = Zmod.unsigned (N.v22483 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22483 s i)) at 1.
  unfold R.v22483, N.v22483.
  unfold R.v6, N.v6.
  rewrite !state_r664_nr_5F664.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r664_nr_5F664 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22484 (s : N.State) (i : N.Inputs) :
  R.v22484 (state s) (inputs i) = Zmod.unsigned (N.v22484 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22484 s i)) at 1.
  unfold R.v22484, N.v22484.
  rewrite ?node_22482.
  rewrite ?node_22483.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22485 (s : N.State) (i : N.Inputs) :
  R.v22485 (state s) (inputs i) = Zmod.unsigned (N.v22485 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22485 s i)) at 1.
  unfold R.v22485, N.v22485.
  unfold R.v16484, N.v16484.
  rewrite ?node_22484.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22486 (s : N.State) (i : N.Inputs) :
  R.v22486 (state s) (inputs i) = Zmod.unsigned (N.v22486 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22486 s i)) at 1.
  unfold R.v22486, N.v22486.
  rewrite ?node_22481.
  rewrite ?node_22485.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22487 (s : N.State) (i : N.Inputs) :
  R.v22487 (state s) (inputs i) = Zmod.unsigned (N.v22487 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22487 s i)) at 1.
  unfold R.v22487, N.v22487.
  unfold R.v6, N.v6.
  rewrite ?node_22486.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22488 (s : N.State) (i : N.Inputs) :
  R.v22488 (state s) (inputs i) = Zmod.unsigned (N.v22488 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22488 s i)) at 1.
  unfold R.v22488, N.v22488.
  rewrite ?node_8089.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22489 (s : N.State) (i : N.Inputs) :
  R.v22489 (state s) (inputs i) = Zmod.unsigned (N.v22489 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22489 s i)) at 1.
  unfold R.v22489, N.v22489.
  unfold R.v6, N.v6.
  rewrite ?node_8213.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22490 (s : N.State) (i : N.Inputs) :
  R.v22490 (state s) (inputs i) = Zmod.unsigned (N.v22490 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22490 s i)) at 1.
  unfold R.v22490, N.v22490.
  rewrite ?node_22488.
  rewrite ?node_22489.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22491 (s : N.State) (i : N.Inputs) :
  R.v22491 (state s) (inputs i) = Zmod.unsigned (N.v22491 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22491 s i)) at 1.
  unfold R.v22491, N.v22491.
  rewrite ?node_22487.
  rewrite ?node_22490.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22492 (s : N.State) (i : N.Inputs) :
  R.v22492 (state s) (inputs i) = Zmod.unsigned (N.v22492 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22492 s i)) at 1.
  unfold R.v22492, N.v22492.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22493 (s : N.State) (i : N.Inputs) :
  R.v22493 (state s) (inputs i) = Zmod.unsigned (N.v22493 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22493 s i)) at 1.
  unfold R.v22493, N.v22493.
  rewrite ?node_8093.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22494 (s : N.State) (i : N.Inputs) :
  R.v22494 (state s) (inputs i) = Zmod.unsigned (N.v22494 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22494 s i)) at 1.
  unfold R.v22494, N.v22494.
  unfold R.v6, N.v6.
  rewrite !state_r667_nr_5F667.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r667_nr_5F667 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22495 (s : N.State) (i : N.Inputs) :
  R.v22495 (state s) (inputs i) = Zmod.unsigned (N.v22495 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22495 s i)) at 1.
  unfold R.v22495, N.v22495.
  unfold R.v6, N.v6.
  rewrite ?node_8089.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22496 (s : N.State) (i : N.Inputs) :
  R.v22496 (state s) (inputs i) = Zmod.unsigned (N.v22496 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22496 s i)) at 1.
  unfold R.v22496, N.v22496.
  rewrite ?node_22494.
  rewrite ?node_22495.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22497 (s : N.State) (i : N.Inputs) :
  R.v22497 (state s) (inputs i) = Zmod.unsigned (N.v22497 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22497 s i)) at 1.
  unfold R.v22497, N.v22497.
  unfold R.v16484, N.v16484.
  rewrite ?node_22496.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22498 (s : N.State) (i : N.Inputs) :
  R.v22498 (state s) (inputs i) = Zmod.unsigned (N.v22498 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22498 s i)) at 1.
  unfold R.v22498, N.v22498.
  rewrite ?node_22493.
  rewrite ?node_22497.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22499 (s : N.State) (i : N.Inputs) :
  R.v22499 (state s) (inputs i) = Zmod.unsigned (N.v22499 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22499 s i)) at 1.
  unfold R.v22499, N.v22499.
  unfold R.v6, N.v6.
  rewrite ?node_22498.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22500 (s : N.State) (i : N.Inputs) :
  R.v22500 (state s) (inputs i) = Zmod.unsigned (N.v22500 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22500 s i)) at 1.
  unfold R.v22500, N.v22500.
  rewrite ?node_8094.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22501 (s : N.State) (i : N.Inputs) :
  R.v22501 (state s) (inputs i) = Zmod.unsigned (N.v22501 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22501 s i)) at 1.
  unfold R.v22501, N.v22501.
  unfold R.v6, N.v6.
  rewrite ?node_8247.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22502 (s : N.State) (i : N.Inputs) :
  R.v22502 (state s) (inputs i) = Zmod.unsigned (N.v22502 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22502 s i)) at 1.
  unfold R.v22502, N.v22502.
  rewrite ?node_22500.
  rewrite ?node_22501.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22503 (s : N.State) (i : N.Inputs) :
  R.v22503 (state s) (inputs i) = Zmod.unsigned (N.v22503 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22503 s i)) at 1.
  unfold R.v22503, N.v22503.
  rewrite ?node_22499.
  rewrite ?node_22502.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22504 (s : N.State) (i : N.Inputs) :
  R.v22504 (state s) (inputs i) = Zmod.unsigned (N.v22504 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22504 s i)) at 1.
  unfold R.v22504, N.v22504.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22505 (s : N.State) (i : N.Inputs) :
  R.v22505 (state s) (inputs i) = Zmod.unsigned (N.v22505 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22505 s i)) at 1.
  unfold R.v22505, N.v22505.
  rewrite ?node_8100.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22506 (s : N.State) (i : N.Inputs) :
  R.v22506 (state s) (inputs i) = Zmod.unsigned (N.v22506 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22506 s i)) at 1.
  unfold R.v22506, N.v22506.
  unfold R.v16463, N.v16463.
  rewrite !state_r671_nr_5F671.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r671_nr_5F671 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22507 (s : N.State) (i : N.Inputs) :
  R.v22507 (state s) (inputs i) = Zmod.unsigned (N.v22507 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22507 s i)) at 1.
  unfold R.v22507, N.v22507.
  unfold R.v16463, N.v16463.
  rewrite !state_r670_nr_5F670.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r670_nr_5F670 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22508 (s : N.State) (i : N.Inputs) :
  R.v22508 (state s) (inputs i) = Zmod.unsigned (N.v22508 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22508 s i)) at 1.
  unfold R.v22508, N.v22508.
  unfold R.v6, N.v6.
  rewrite !state_r669_nr_5F669.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r669_nr_5F669 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22509 (s : N.State) (i : N.Inputs) :
  R.v22509 (state s) (inputs i) = Zmod.unsigned (N.v22509 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22509 s i)) at 1.
  unfold R.v22509, N.v22509.
  unfold R.v6, N.v6.
  rewrite !state_r668_nr_5F668.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r668_nr_5F668 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22510 (s : N.State) (i : N.Inputs) :
  R.v22510 (state s) (inputs i) = Zmod.unsigned (N.v22510 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22510 s i)) at 1.
  unfold R.v22510, N.v22510.
  rewrite ?node_22508.
  rewrite ?node_22509.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22511 (s : N.State) (i : N.Inputs) :
  R.v22511 (state s) (inputs i) = Zmod.unsigned (N.v22511 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22511 s i)) at 1.
  unfold R.v22511, N.v22511.
  unfold R.v16484, N.v16484.
  rewrite ?node_22510.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22512 (s : N.State) (i : N.Inputs) :
  R.v22512 (state s) (inputs i) = Zmod.unsigned (N.v22512 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22512 s i)) at 1.
  unfold R.v22512, N.v22512.
  rewrite ?node_22505.
  rewrite ?node_22506.
  rewrite ?node_22507.
  rewrite ?node_22511.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22513 (s : N.State) (i : N.Inputs) :
  R.v22513 (state s) (inputs i) = Zmod.unsigned (N.v22513 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22513 s i)) at 1.
  unfold R.v22513, N.v22513.
  unfold R.v6, N.v6.
  rewrite ?node_22512.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22514 (s : N.State) (i : N.Inputs) :
  R.v22514 (state s) (inputs i) = Zmod.unsigned (N.v22514 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22514 s i)) at 1.
  unfold R.v22514, N.v22514.
  rewrite ?node_8101.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22515 (s : N.State) (i : N.Inputs) :
  R.v22515 (state s) (inputs i) = Zmod.unsigned (N.v22515 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22515 s i)) at 1.
  unfold R.v22515, N.v22515.
  unfold R.v6, N.v6.
  rewrite ?node_8220.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22516 (s : N.State) (i : N.Inputs) :
  R.v22516 (state s) (inputs i) = Zmod.unsigned (N.v22516 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22516 s i)) at 1.
  unfold R.v22516, N.v22516.
  unfold R.v6, N.v6.
  rewrite ?node_8256.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22517 (s : N.State) (i : N.Inputs) :
  R.v22517 (state s) (inputs i) = Zmod.unsigned (N.v22517 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22517 s i)) at 1.
  unfold R.v22517, N.v22517.
  rewrite ?node_22514.
  rewrite ?node_22515.
  rewrite ?node_22516.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22518 (s : N.State) (i : N.Inputs) :
  R.v22518 (state s) (inputs i) = Zmod.unsigned (N.v22518 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22518 s i)) at 1.
  unfold R.v22518, N.v22518.
  rewrite ?node_22513.
  rewrite ?node_22517.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22519 (s : N.State) (i : N.Inputs) :
  R.v22519 (state s) (inputs i) = Zmod.unsigned (N.v22519 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22519 s i)) at 1.
  unfold R.v22519, N.v22519.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22520 (s : N.State) (i : N.Inputs) :
  R.v22520 (state s) (inputs i) = Zmod.unsigned (N.v22520 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22520 s i)) at 1.
  unfold R.v22520, N.v22520.
  unfold R.v16463, N.v16463.
  rewrite !state_r670_nr_5F670.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r670_nr_5F670 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22521 (s : N.State) (i : N.Inputs) :
  R.v22521 (state s) (inputs i) = Zmod.unsigned (N.v22521 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22521 s i)) at 1.
  unfold R.v22521, N.v22521.
  unfold R.v6, N.v6.
  rewrite !state_r669_nr_5F669.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r669_nr_5F669 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22522 (s : N.State) (i : N.Inputs) :
  R.v22522 (state s) (inputs i) = Zmod.unsigned (N.v22522 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22522 s i)) at 1.
  unfold R.v22522, N.v22522.
  unfold R.v6, N.v6.
  rewrite !state_r668_nr_5F668.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r668_nr_5F668 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22523 (s : N.State) (i : N.Inputs) :
  R.v22523 (state s) (inputs i) = Zmod.unsigned (N.v22523 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22523 s i)) at 1.
  unfold R.v22523, N.v22523.
  rewrite ?node_22521.
  rewrite ?node_22522.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22524 (s : N.State) (i : N.Inputs) :
  R.v22524 (state s) (inputs i) = Zmod.unsigned (N.v22524 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22524 s i)) at 1.
  unfold R.v22524, N.v22524.
  unfold R.v16484, N.v16484.
  rewrite ?node_22523.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22525 (s : N.State) (i : N.Inputs) :
  R.v22525 (state s) (inputs i) = Zmod.unsigned (N.v22525 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22525 s i)) at 1.
  unfold R.v22525, N.v22525.
  rewrite ?node_22520.
  rewrite ?node_22524.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22526 (s : N.State) (i : N.Inputs) :
  R.v22526 (state s) (inputs i) = Zmod.unsigned (N.v22526 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22526 s i)) at 1.
  unfold R.v22526, N.v22526.
  unfold R.v6, N.v6.
  rewrite ?node_22525.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22527 (s : N.State) (i : N.Inputs) :
  R.v22527 (state s) (inputs i) = Zmod.unsigned (N.v22527 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22527 s i)) at 1.
  unfold R.v22527, N.v22527.
  rewrite ?node_8096.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22528 (s : N.State) (i : N.Inputs) :
  R.v22528 (state s) (inputs i) = Zmod.unsigned (N.v22528 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22528 s i)) at 1.
  unfold R.v22528, N.v22528.
  unfold R.v6, N.v6.
  rewrite ?node_8220.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22529 (s : N.State) (i : N.Inputs) :
  R.v22529 (state s) (inputs i) = Zmod.unsigned (N.v22529 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22529 s i)) at 1.
  unfold R.v22529, N.v22529.
  rewrite ?node_22527.
  rewrite ?node_22528.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22530 (s : N.State) (i : N.Inputs) :
  R.v22530 (state s) (inputs i) = Zmod.unsigned (N.v22530 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22530 s i)) at 1.
  unfold R.v22530, N.v22530.
  rewrite ?node_22526.
  rewrite ?node_22529.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22531 (s : N.State) (i : N.Inputs) :
  R.v22531 (state s) (inputs i) = Zmod.unsigned (N.v22531 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22531 s i)) at 1.
  unfold R.v22531, N.v22531.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22532 (s : N.State) (i : N.Inputs) :
  R.v22532 (state s) (inputs i) = Zmod.unsigned (N.v22532 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22532 s i)) at 1.
  unfold R.v22532, N.v22532.
  rewrite ?node_8100.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22533 (s : N.State) (i : N.Inputs) :
  R.v22533 (state s) (inputs i) = Zmod.unsigned (N.v22533 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22533 s i)) at 1.
  unfold R.v22533, N.v22533.
  unfold R.v6, N.v6.
  rewrite !state_r671_nr_5F671.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r671_nr_5F671 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22534 (s : N.State) (i : N.Inputs) :
  R.v22534 (state s) (inputs i) = Zmod.unsigned (N.v22534 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22534 s i)) at 1.
  unfold R.v22534, N.v22534.
  unfold R.v6, N.v6.
  rewrite ?node_8096.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22535 (s : N.State) (i : N.Inputs) :
  R.v22535 (state s) (inputs i) = Zmod.unsigned (N.v22535 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22535 s i)) at 1.
  unfold R.v22535, N.v22535.
  rewrite ?node_22533.
  rewrite ?node_22534.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22536 (s : N.State) (i : N.Inputs) :
  R.v22536 (state s) (inputs i) = Zmod.unsigned (N.v22536 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22536 s i)) at 1.
  unfold R.v22536, N.v22536.
  unfold R.v16484, N.v16484.
  rewrite ?node_22535.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22537 (s : N.State) (i : N.Inputs) :
  R.v22537 (state s) (inputs i) = Zmod.unsigned (N.v22537 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22537 s i)) at 1.
  unfold R.v22537, N.v22537.
  rewrite ?node_22532.
  rewrite ?node_22536.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22538 (s : N.State) (i : N.Inputs) :
  R.v22538 (state s) (inputs i) = Zmod.unsigned (N.v22538 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22538 s i)) at 1.
  unfold R.v22538, N.v22538.
  unfold R.v6, N.v6.
  rewrite ?node_22537.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22539 (s : N.State) (i : N.Inputs) :
  R.v22539 (state s) (inputs i) = Zmod.unsigned (N.v22539 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22539 s i)) at 1.
  unfold R.v22539, N.v22539.
  rewrite ?node_8101.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22540 (s : N.State) (i : N.Inputs) :
  R.v22540 (state s) (inputs i) = Zmod.unsigned (N.v22540 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22540 s i)) at 1.
  unfold R.v22540, N.v22540.
  unfold R.v6, N.v6.
  rewrite ?node_8256.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22541 (s : N.State) (i : N.Inputs) :
  R.v22541 (state s) (inputs i) = Zmod.unsigned (N.v22541 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22541 s i)) at 1.
  unfold R.v22541, N.v22541.
  rewrite ?node_22539.
  rewrite ?node_22540.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22542 (s : N.State) (i : N.Inputs) :
  R.v22542 (state s) (inputs i) = Zmod.unsigned (N.v22542 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22542 s i)) at 1.
  unfold R.v22542, N.v22542.
  rewrite ?node_22538.
  rewrite ?node_22541.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22543 (s : N.State) (i : N.Inputs) :
  R.v22543 (state s) (inputs i) = Zmod.unsigned (N.v22543 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22543 s i)) at 1.
  unfold R.v22543, N.v22543.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22544 (s : N.State) (i : N.Inputs) :
  R.v22544 (state s) (inputs i) = Zmod.unsigned (N.v22544 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22544 s i)) at 1.
  unfold R.v22544, N.v22544.
  unfold R.v6, N.v6.
  rewrite !state_r673_nr_5F673.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r673_nr_5F673 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22545 (s : N.State) (i : N.Inputs) :
  R.v22545 (state s) (inputs i) = Zmod.unsigned (N.v22545 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22545 s i)) at 1.
  unfold R.v22545, N.v22545.
  unfold R.v6, N.v6.
  rewrite !state_r672_nr_5F672.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r672_nr_5F672 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22546 (s : N.State) (i : N.Inputs) :
  R.v22546 (state s) (inputs i) = Zmod.unsigned (N.v22546 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22546 s i)) at 1.
  unfold R.v22546, N.v22546.
  rewrite ?node_22544.
  rewrite ?node_22545.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22547 (s : N.State) (i : N.Inputs) :
  R.v22547 (state s) (inputs i) = Zmod.unsigned (N.v22547 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22547 s i)) at 1.
  unfold R.v22547, N.v22547.
  unfold R.v16463, N.v16463.
  rewrite ?node_22546.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22548 (s : N.State) (i : N.Inputs) :
  R.v22548 (state s) (inputs i) = Zmod.unsigned (N.v22548 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22548 s i)) at 1.
  unfold R.v22548, N.v22548.
  rewrite ?node_8103.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22549 (s : N.State) (i : N.Inputs) :
  R.v22549 (state s) (inputs i) = Zmod.unsigned (N.v22549 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22549 s i)) at 1.
  unfold R.v22549, N.v22549.
  unfold R.v6, N.v6.
  rewrite ?node_8257.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22550 (s : N.State) (i : N.Inputs) :
  R.v22550 (state s) (inputs i) = Zmod.unsigned (N.v22550 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22550 s i)) at 1.
  unfold R.v22550, N.v22550.
  rewrite ?node_22548.
  rewrite ?node_22549.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22551 (s : N.State) (i : N.Inputs) :
  R.v22551 (state s) (inputs i) = Zmod.unsigned (N.v22551 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22551 s i)) at 1.
  unfold R.v22551, N.v22551.
  rewrite ?node_22547.
  rewrite ?node_22550.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22552 (s : N.State) (i : N.Inputs) :
  R.v22552 (state s) (inputs i) = Zmod.unsigned (N.v22552 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22552 s i)) at 1.
  unfold R.v22552, N.v22552.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22553 (s : N.State) (i : N.Inputs) :
  R.v22553 (state s) (inputs i) = Zmod.unsigned (N.v22553 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22553 s i)) at 1.
  unfold R.v22553, N.v22553.
  rewrite ?node_8178.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22554 (s : N.State) (i : N.Inputs) :
  R.v22554 (state s) (inputs i) = Zmod.unsigned (N.v22554 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22554 s i)) at 1.
  unfold R.v22554, N.v22554.
  unfold R.v16463, N.v16463.
  rewrite !state_r677_nr_5F677.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r677_nr_5F677 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22555 (s : N.State) (i : N.Inputs) :
  R.v22555 (state s) (inputs i) = Zmod.unsigned (N.v22555 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22555 s i)) at 1.
  unfold R.v22555, N.v22555.
  unfold R.v16463, N.v16463.
  rewrite !state_r676_nr_5F676.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r676_nr_5F676 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22556 (s : N.State) (i : N.Inputs) :
  R.v22556 (state s) (inputs i) = Zmod.unsigned (N.v22556 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22556 s i)) at 1.
  unfold R.v22556, N.v22556.
  unfold R.v6, N.v6.
  rewrite !state_r675_nr_5F675.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r675_nr_5F675 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22557 (s : N.State) (i : N.Inputs) :
  R.v22557 (state s) (inputs i) = Zmod.unsigned (N.v22557 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22557 s i)) at 1.
  unfold R.v22557, N.v22557.
  unfold R.v6, N.v6.
  rewrite !state_r674_nr_5F674.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r674_nr_5F674 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22558 (s : N.State) (i : N.Inputs) :
  R.v22558 (state s) (inputs i) = Zmod.unsigned (N.v22558 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22558 s i)) at 1.
  unfold R.v22558, N.v22558.
  rewrite ?node_22556.
  rewrite ?node_22557.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22559 (s : N.State) (i : N.Inputs) :
  R.v22559 (state s) (inputs i) = Zmod.unsigned (N.v22559 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22559 s i)) at 1.
  unfold R.v22559, N.v22559.
  unfold R.v16484, N.v16484.
  rewrite ?node_22558.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22560 (s : N.State) (i : N.Inputs) :
  R.v22560 (state s) (inputs i) = Zmod.unsigned (N.v22560 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22560 s i)) at 1.
  unfold R.v22560, N.v22560.
  rewrite ?node_22553.
  rewrite ?node_22554.
  rewrite ?node_22555.
  rewrite ?node_22559.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22561 (s : N.State) (i : N.Inputs) :
  R.v22561 (state s) (inputs i) = Zmod.unsigned (N.v22561 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22561 s i)) at 1.
  unfold R.v22561, N.v22561.
  unfold R.v6, N.v6.
  rewrite ?node_22560.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22562 (s : N.State) (i : N.Inputs) :
  R.v22562 (state s) (inputs i) = Zmod.unsigned (N.v22562 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22562 s i)) at 1.
  unfold R.v22562, N.v22562.
  rewrite ?node_8179.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22563 (s : N.State) (i : N.Inputs) :
  R.v22563 (state s) (inputs i) = Zmod.unsigned (N.v22563 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22563 s i)) at 1.
  unfold R.v22563, N.v22563.
  unfold R.v6, N.v6.
  rewrite ?node_8300.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22564 (s : N.State) (i : N.Inputs) :
  R.v22564 (state s) (inputs i) = Zmod.unsigned (N.v22564 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22564 s i)) at 1.
  unfold R.v22564, N.v22564.
  unfold R.v6, N.v6.
  rewrite ?node_8350.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22565 (s : N.State) (i : N.Inputs) :
  R.v22565 (state s) (inputs i) = Zmod.unsigned (N.v22565 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22565 s i)) at 1.
  unfold R.v22565, N.v22565.
  rewrite ?node_22562.
  rewrite ?node_22563.
  rewrite ?node_22564.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22566 (s : N.State) (i : N.Inputs) :
  R.v22566 (state s) (inputs i) = Zmod.unsigned (N.v22566 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22566 s i)) at 1.
  unfold R.v22566, N.v22566.
  rewrite ?node_22561.
  rewrite ?node_22565.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22567 (s : N.State) (i : N.Inputs) :
  R.v22567 (state s) (inputs i) = Zmod.unsigned (N.v22567 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22567 s i)) at 1.
  unfold R.v22567, N.v22567.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22568 (s : N.State) (i : N.Inputs) :
  R.v22568 (state s) (inputs i) = Zmod.unsigned (N.v22568 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22568 s i)) at 1.
  unfold R.v22568, N.v22568.
  unfold R.v16463, N.v16463.
  rewrite !state_r676_nr_5F676.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r676_nr_5F676 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22569 (s : N.State) (i : N.Inputs) :
  R.v22569 (state s) (inputs i) = Zmod.unsigned (N.v22569 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22569 s i)) at 1.
  unfold R.v22569, N.v22569.
  unfold R.v6, N.v6.
  rewrite !state_r675_nr_5F675.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r675_nr_5F675 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22570 (s : N.State) (i : N.Inputs) :
  R.v22570 (state s) (inputs i) = Zmod.unsigned (N.v22570 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22570 s i)) at 1.
  unfold R.v22570, N.v22570.
  unfold R.v6, N.v6.
  rewrite !state_r674_nr_5F674.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r674_nr_5F674 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22571 (s : N.State) (i : N.Inputs) :
  R.v22571 (state s) (inputs i) = Zmod.unsigned (N.v22571 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22571 s i)) at 1.
  unfold R.v22571, N.v22571.
  rewrite ?node_22569.
  rewrite ?node_22570.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22572 (s : N.State) (i : N.Inputs) :
  R.v22572 (state s) (inputs i) = Zmod.unsigned (N.v22572 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22572 s i)) at 1.
  unfold R.v22572, N.v22572.
  unfold R.v16484, N.v16484.
  rewrite ?node_22571.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22573 (s : N.State) (i : N.Inputs) :
  R.v22573 (state s) (inputs i) = Zmod.unsigned (N.v22573 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22573 s i)) at 1.
  unfold R.v22573, N.v22573.
  rewrite ?node_22568.
  rewrite ?node_22572.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22574 (s : N.State) (i : N.Inputs) :
  R.v22574 (state s) (inputs i) = Zmod.unsigned (N.v22574 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22574 s i)) at 1.
  unfold R.v22574, N.v22574.
  unfold R.v6, N.v6.
  rewrite ?node_22573.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22575 (s : N.State) (i : N.Inputs) :
  R.v22575 (state s) (inputs i) = Zmod.unsigned (N.v22575 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22575 s i)) at 1.
  unfold R.v22575, N.v22575.
  rewrite ?node_8174.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22576 (s : N.State) (i : N.Inputs) :
  R.v22576 (state s) (inputs i) = Zmod.unsigned (N.v22576 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22576 s i)) at 1.
  unfold R.v22576, N.v22576.
  unfold R.v6, N.v6.
  rewrite ?node_8300.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22577 (s : N.State) (i : N.Inputs) :
  R.v22577 (state s) (inputs i) = Zmod.unsigned (N.v22577 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22577 s i)) at 1.
  unfold R.v22577, N.v22577.
  rewrite ?node_22575.
  rewrite ?node_22576.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22578 (s : N.State) (i : N.Inputs) :
  R.v22578 (state s) (inputs i) = Zmod.unsigned (N.v22578 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22578 s i)) at 1.
  unfold R.v22578, N.v22578.
  rewrite ?node_22574.
  rewrite ?node_22577.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22579 (s : N.State) (i : N.Inputs) :
  R.v22579 (state s) (inputs i) = Zmod.unsigned (N.v22579 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22579 s i)) at 1.
  unfold R.v22579, N.v22579.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22580 (s : N.State) (i : N.Inputs) :
  R.v22580 (state s) (inputs i) = Zmod.unsigned (N.v22580 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22580 s i)) at 1.
  unfold R.v22580, N.v22580.
  rewrite ?node_8178.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22581 (s : N.State) (i : N.Inputs) :
  R.v22581 (state s) (inputs i) = Zmod.unsigned (N.v22581 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22581 s i)) at 1.
  unfold R.v22581, N.v22581.
  unfold R.v6, N.v6.
  rewrite !state_r677_nr_5F677.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r677_nr_5F677 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22582 (s : N.State) (i : N.Inputs) :
  R.v22582 (state s) (inputs i) = Zmod.unsigned (N.v22582 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22582 s i)) at 1.
  unfold R.v22582, N.v22582.
  unfold R.v6, N.v6.
  rewrite ?node_8174.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22583 (s : N.State) (i : N.Inputs) :
  R.v22583 (state s) (inputs i) = Zmod.unsigned (N.v22583 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22583 s i)) at 1.
  unfold R.v22583, N.v22583.
  rewrite ?node_22581.
  rewrite ?node_22582.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22584 (s : N.State) (i : N.Inputs) :
  R.v22584 (state s) (inputs i) = Zmod.unsigned (N.v22584 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22584 s i)) at 1.
  unfold R.v22584, N.v22584.
  unfold R.v16484, N.v16484.
  rewrite ?node_22583.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22585 (s : N.State) (i : N.Inputs) :
  R.v22585 (state s) (inputs i) = Zmod.unsigned (N.v22585 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22585 s i)) at 1.
  unfold R.v22585, N.v22585.
  rewrite ?node_22580.
  rewrite ?node_22584.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22586 (s : N.State) (i : N.Inputs) :
  R.v22586 (state s) (inputs i) = Zmod.unsigned (N.v22586 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22586 s i)) at 1.
  unfold R.v22586, N.v22586.
  unfold R.v6, N.v6.
  rewrite ?node_22585.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22587 (s : N.State) (i : N.Inputs) :
  R.v22587 (state s) (inputs i) = Zmod.unsigned (N.v22587 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22587 s i)) at 1.
  unfold R.v22587, N.v22587.
  rewrite ?node_8179.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22588 (s : N.State) (i : N.Inputs) :
  R.v22588 (state s) (inputs i) = Zmod.unsigned (N.v22588 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22588 s i)) at 1.
  unfold R.v22588, N.v22588.
  unfold R.v6, N.v6.
  rewrite ?node_8350.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22589 (s : N.State) (i : N.Inputs) :
  R.v22589 (state s) (inputs i) = Zmod.unsigned (N.v22589 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22589 s i)) at 1.
  unfold R.v22589, N.v22589.
  rewrite ?node_22587.
  rewrite ?node_22588.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22590 (s : N.State) (i : N.Inputs) :
  R.v22590 (state s) (inputs i) = Zmod.unsigned (N.v22590 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22590 s i)) at 1.
  unfold R.v22590, N.v22590.
  rewrite ?node_22586.
  rewrite ?node_22589.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22591 (s : N.State) (i : N.Inputs) :
  R.v22591 (state s) (inputs i) = Zmod.unsigned (N.v22591 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22591 s i)) at 1.
  unfold R.v22591, N.v22591.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22592 (s : N.State) (i : N.Inputs) :
  R.v22592 (state s) (inputs i) = Zmod.unsigned (N.v22592 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22592 s i)) at 1.
  unfold R.v22592, N.v22592.
  rewrite ?node_8185.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22593 (s : N.State) (i : N.Inputs) :
  R.v22593 (state s) (inputs i) = Zmod.unsigned (N.v22593 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22593 s i)) at 1.
  unfold R.v22593, N.v22593.
  unfold R.v16463, N.v16463.
  rewrite !state_r681_nr_5F681.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r681_nr_5F681 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22594 (s : N.State) (i : N.Inputs) :
  R.v22594 (state s) (inputs i) = Zmod.unsigned (N.v22594 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22594 s i)) at 1.
  unfold R.v22594, N.v22594.
  unfold R.v16463, N.v16463.
  rewrite !state_r680_nr_5F680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r680_nr_5F680 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22595 (s : N.State) (i : N.Inputs) :
  R.v22595 (state s) (inputs i) = Zmod.unsigned (N.v22595 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22595 s i)) at 1.
  unfold R.v22595, N.v22595.
  unfold R.v6, N.v6.
  rewrite !state_r679_nr_5F679.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r679_nr_5F679 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22596 (s : N.State) (i : N.Inputs) :
  R.v22596 (state s) (inputs i) = Zmod.unsigned (N.v22596 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22596 s i)) at 1.
  unfold R.v22596, N.v22596.
  unfold R.v6, N.v6.
  rewrite !state_r678_nr_5F678.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r678_nr_5F678 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22597 (s : N.State) (i : N.Inputs) :
  R.v22597 (state s) (inputs i) = Zmod.unsigned (N.v22597 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22597 s i)) at 1.
  unfold R.v22597, N.v22597.
  rewrite ?node_22595.
  rewrite ?node_22596.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22598 (s : N.State) (i : N.Inputs) :
  R.v22598 (state s) (inputs i) = Zmod.unsigned (N.v22598 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22598 s i)) at 1.
  unfold R.v22598, N.v22598.
  unfold R.v16484, N.v16484.
  rewrite ?node_22597.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22599 (s : N.State) (i : N.Inputs) :
  R.v22599 (state s) (inputs i) = Zmod.unsigned (N.v22599 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22599 s i)) at 1.
  unfold R.v22599, N.v22599.
  rewrite ?node_22592.
  rewrite ?node_22593.
  rewrite ?node_22594.
  rewrite ?node_22598.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22600 (s : N.State) (i : N.Inputs) :
  R.v22600 (state s) (inputs i) = Zmod.unsigned (N.v22600 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22600 s i)) at 1.
  unfold R.v22600, N.v22600.
  unfold R.v6, N.v6.
  rewrite ?node_22599.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22601 (s : N.State) (i : N.Inputs) :
  R.v22601 (state s) (inputs i) = Zmod.unsigned (N.v22601 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22601 s i)) at 1.
  unfold R.v22601, N.v22601.
  rewrite ?node_8186.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22602 (s : N.State) (i : N.Inputs) :
  R.v22602 (state s) (inputs i) = Zmod.unsigned (N.v22602 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22602 s i)) at 1.
  unfold R.v22602, N.v22602.
  unfold R.v6, N.v6.
  rewrite ?node_8307.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22603 (s : N.State) (i : N.Inputs) :
  R.v22603 (state s) (inputs i) = Zmod.unsigned (N.v22603 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22603 s i)) at 1.
  unfold R.v22603, N.v22603.
  unfold R.v6, N.v6.
  rewrite ?node_8359.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22604 (s : N.State) (i : N.Inputs) :
  R.v22604 (state s) (inputs i) = Zmod.unsigned (N.v22604 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22604 s i)) at 1.
  unfold R.v22604, N.v22604.
  rewrite ?node_22601.
  rewrite ?node_22602.
  rewrite ?node_22603.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22605 (s : N.State) (i : N.Inputs) :
  R.v22605 (state s) (inputs i) = Zmod.unsigned (N.v22605 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22605 s i)) at 1.
  unfold R.v22605, N.v22605.
  rewrite ?node_22600.
  rewrite ?node_22604.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22606 (s : N.State) (i : N.Inputs) :
  R.v22606 (state s) (inputs i) = Zmod.unsigned (N.v22606 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22606 s i)) at 1.
  unfold R.v22606, N.v22606.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22607 (s : N.State) (i : N.Inputs) :
  R.v22607 (state s) (inputs i) = Zmod.unsigned (N.v22607 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22607 s i)) at 1.
  unfold R.v22607, N.v22607.
  unfold R.v16463, N.v16463.
  rewrite !state_r680_nr_5F680.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r680_nr_5F680 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22608 (s : N.State) (i : N.Inputs) :
  R.v22608 (state s) (inputs i) = Zmod.unsigned (N.v22608 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22608 s i)) at 1.
  unfold R.v22608, N.v22608.
  unfold R.v6, N.v6.
  rewrite !state_r679_nr_5F679.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r679_nr_5F679 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22609 (s : N.State) (i : N.Inputs) :
  R.v22609 (state s) (inputs i) = Zmod.unsigned (N.v22609 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22609 s i)) at 1.
  unfold R.v22609, N.v22609.
  unfold R.v6, N.v6.
  rewrite !state_r678_nr_5F678.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r678_nr_5F678 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22610 (s : N.State) (i : N.Inputs) :
  R.v22610 (state s) (inputs i) = Zmod.unsigned (N.v22610 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22610 s i)) at 1.
  unfold R.v22610, N.v22610.
  rewrite ?node_22608.
  rewrite ?node_22609.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22611 (s : N.State) (i : N.Inputs) :
  R.v22611 (state s) (inputs i) = Zmod.unsigned (N.v22611 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22611 s i)) at 1.
  unfold R.v22611, N.v22611.
  unfold R.v16484, N.v16484.
  rewrite ?node_22610.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22612 (s : N.State) (i : N.Inputs) :
  R.v22612 (state s) (inputs i) = Zmod.unsigned (N.v22612 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22612 s i)) at 1.
  unfold R.v22612, N.v22612.
  rewrite ?node_22607.
  rewrite ?node_22611.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22613 (s : N.State) (i : N.Inputs) :
  R.v22613 (state s) (inputs i) = Zmod.unsigned (N.v22613 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22613 s i)) at 1.
  unfold R.v22613, N.v22613.
  unfold R.v6, N.v6.
  rewrite ?node_22612.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22614 (s : N.State) (i : N.Inputs) :
  R.v22614 (state s) (inputs i) = Zmod.unsigned (N.v22614 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22614 s i)) at 1.
  unfold R.v22614, N.v22614.
  rewrite ?node_8181.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22615 (s : N.State) (i : N.Inputs) :
  R.v22615 (state s) (inputs i) = Zmod.unsigned (N.v22615 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22615 s i)) at 1.
  unfold R.v22615, N.v22615.
  unfold R.v6, N.v6.
  rewrite ?node_8307.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22616 (s : N.State) (i : N.Inputs) :
  R.v22616 (state s) (inputs i) = Zmod.unsigned (N.v22616 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22616 s i)) at 1.
  unfold R.v22616, N.v22616.
  rewrite ?node_22614.
  rewrite ?node_22615.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22617 (s : N.State) (i : N.Inputs) :
  R.v22617 (state s) (inputs i) = Zmod.unsigned (N.v22617 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22617 s i)) at 1.
  unfold R.v22617, N.v22617.
  rewrite ?node_22613.
  rewrite ?node_22616.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22618 (s : N.State) (i : N.Inputs) :
  R.v22618 (state s) (inputs i) = Zmod.unsigned (N.v22618 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22618 s i)) at 1.
  unfold R.v22618, N.v22618.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22619 (s : N.State) (i : N.Inputs) :
  R.v22619 (state s) (inputs i) = Zmod.unsigned (N.v22619 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22619 s i)) at 1.
  unfold R.v22619, N.v22619.
  rewrite ?node_8185.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22620 (s : N.State) (i : N.Inputs) :
  R.v22620 (state s) (inputs i) = Zmod.unsigned (N.v22620 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22620 s i)) at 1.
  unfold R.v22620, N.v22620.
  unfold R.v6, N.v6.
  rewrite !state_r681_nr_5F681.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r681_nr_5F681 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22621 (s : N.State) (i : N.Inputs) :
  R.v22621 (state s) (inputs i) = Zmod.unsigned (N.v22621 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22621 s i)) at 1.
  unfold R.v22621, N.v22621.
  unfold R.v6, N.v6.
  rewrite ?node_8181.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22622 (s : N.State) (i : N.Inputs) :
  R.v22622 (state s) (inputs i) = Zmod.unsigned (N.v22622 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22622 s i)) at 1.
  unfold R.v22622, N.v22622.
  rewrite ?node_22620.
  rewrite ?node_22621.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22623 (s : N.State) (i : N.Inputs) :
  R.v22623 (state s) (inputs i) = Zmod.unsigned (N.v22623 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22623 s i)) at 1.
  unfold R.v22623, N.v22623.
  unfold R.v16484, N.v16484.
  rewrite ?node_22622.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22624 (s : N.State) (i : N.Inputs) :
  R.v22624 (state s) (inputs i) = Zmod.unsigned (N.v22624 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22624 s i)) at 1.
  unfold R.v22624, N.v22624.
  rewrite ?node_22619.
  rewrite ?node_22623.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22625 (s : N.State) (i : N.Inputs) :
  R.v22625 (state s) (inputs i) = Zmod.unsigned (N.v22625 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22625 s i)) at 1.
  unfold R.v22625, N.v22625.
  unfold R.v6, N.v6.
  rewrite ?node_22624.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22626 (s : N.State) (i : N.Inputs) :
  R.v22626 (state s) (inputs i) = Zmod.unsigned (N.v22626 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22626 s i)) at 1.
  unfold R.v22626, N.v22626.
  rewrite ?node_8186.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22627 (s : N.State) (i : N.Inputs) :
  R.v22627 (state s) (inputs i) = Zmod.unsigned (N.v22627 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22627 s i)) at 1.
  unfold R.v22627, N.v22627.
  unfold R.v6, N.v6.
  rewrite ?node_8359.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22628 (s : N.State) (i : N.Inputs) :
  R.v22628 (state s) (inputs i) = Zmod.unsigned (N.v22628 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22628 s i)) at 1.
  unfold R.v22628, N.v22628.
  rewrite ?node_22626.
  rewrite ?node_22627.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22629 (s : N.State) (i : N.Inputs) :
  R.v22629 (state s) (inputs i) = Zmod.unsigned (N.v22629 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22629 s i)) at 1.
  unfold R.v22629, N.v22629.
  rewrite ?node_22625.
  rewrite ?node_22628.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22630 (s : N.State) (i : N.Inputs) :
  R.v22630 (state s) (inputs i) = Zmod.unsigned (N.v22630 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22630 s i)) at 1.
  unfold R.v22630, N.v22630.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22631 (s : N.State) (i : N.Inputs) :
  R.v22631 (state s) (inputs i) = Zmod.unsigned (N.v22631 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22631 s i)) at 1.
  unfold R.v22631, N.v22631.
  rewrite ?node_8193.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22632 (s : N.State) (i : N.Inputs) :
  R.v22632 (state s) (inputs i) = Zmod.unsigned (N.v22632 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22632 s i)) at 1.
  unfold R.v22632, N.v22632.
  unfold R.v16463, N.v16463.
  rewrite !state_r685_nr_5F685.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r685_nr_5F685 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22633 (s : N.State) (i : N.Inputs) :
  R.v22633 (state s) (inputs i) = Zmod.unsigned (N.v22633 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22633 s i)) at 1.
  unfold R.v22633, N.v22633.
  unfold R.v16463, N.v16463.
  rewrite !state_r684_nr_5F684.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r684_nr_5F684 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22634 (s : N.State) (i : N.Inputs) :
  R.v22634 (state s) (inputs i) = Zmod.unsigned (N.v22634 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22634 s i)) at 1.
  unfold R.v22634, N.v22634.
  unfold R.v6, N.v6.
  rewrite !state_r683_nr_5F683.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r683_nr_5F683 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22635 (s : N.State) (i : N.Inputs) :
  R.v22635 (state s) (inputs i) = Zmod.unsigned (N.v22635 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22635 s i)) at 1.
  unfold R.v22635, N.v22635.
  unfold R.v6, N.v6.
  rewrite !state_r682_nr_5F682.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r682_nr_5F682 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22636 (s : N.State) (i : N.Inputs) :
  R.v22636 (state s) (inputs i) = Zmod.unsigned (N.v22636 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22636 s i)) at 1.
  unfold R.v22636, N.v22636.
  rewrite ?node_22634.
  rewrite ?node_22635.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22637 (s : N.State) (i : N.Inputs) :
  R.v22637 (state s) (inputs i) = Zmod.unsigned (N.v22637 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22637 s i)) at 1.
  unfold R.v22637, N.v22637.
  unfold R.v16484, N.v16484.
  rewrite ?node_22636.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22638 (s : N.State) (i : N.Inputs) :
  R.v22638 (state s) (inputs i) = Zmod.unsigned (N.v22638 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22638 s i)) at 1.
  unfold R.v22638, N.v22638.
  rewrite ?node_22631.
  rewrite ?node_22632.
  rewrite ?node_22633.
  rewrite ?node_22637.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22639 (s : N.State) (i : N.Inputs) :
  R.v22639 (state s) (inputs i) = Zmod.unsigned (N.v22639 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22639 s i)) at 1.
  unfold R.v22639, N.v22639.
  unfold R.v6, N.v6.
  rewrite ?node_22638.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22640 (s : N.State) (i : N.Inputs) :
  R.v22640 (state s) (inputs i) = Zmod.unsigned (N.v22640 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22640 s i)) at 1.
  unfold R.v22640, N.v22640.
  rewrite ?node_8194.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22641 (s : N.State) (i : N.Inputs) :
  R.v22641 (state s) (inputs i) = Zmod.unsigned (N.v22641 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22641 s i)) at 1.
  unfold R.v22641, N.v22641.
  unfold R.v6, N.v6.
  rewrite ?node_8315.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22642 (s : N.State) (i : N.Inputs) :
  R.v22642 (state s) (inputs i) = Zmod.unsigned (N.v22642 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22642 s i)) at 1.
  unfold R.v22642, N.v22642.
  unfold R.v6, N.v6.
  rewrite ?node_8362.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22643 (s : N.State) (i : N.Inputs) :
  R.v22643 (state s) (inputs i) = Zmod.unsigned (N.v22643 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22643 s i)) at 1.
  unfold R.v22643, N.v22643.
  rewrite ?node_22640.
  rewrite ?node_22641.
  rewrite ?node_22642.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22644 (s : N.State) (i : N.Inputs) :
  R.v22644 (state s) (inputs i) = Zmod.unsigned (N.v22644 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22644 s i)) at 1.
  unfold R.v22644, N.v22644.
  rewrite ?node_22639.
  rewrite ?node_22643.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22645 (s : N.State) (i : N.Inputs) :
  R.v22645 (state s) (inputs i) = Zmod.unsigned (N.v22645 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22645 s i)) at 1.
  unfold R.v22645, N.v22645.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22646 (s : N.State) (i : N.Inputs) :
  R.v22646 (state s) (inputs i) = Zmod.unsigned (N.v22646 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22646 s i)) at 1.
  unfold R.v22646, N.v22646.
  unfold R.v16463, N.v16463.
  rewrite !state_r684_nr_5F684.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r684_nr_5F684 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22647 (s : N.State) (i : N.Inputs) :
  R.v22647 (state s) (inputs i) = Zmod.unsigned (N.v22647 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22647 s i)) at 1.
  unfold R.v22647, N.v22647.
  unfold R.v6, N.v6.
  rewrite !state_r683_nr_5F683.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r683_nr_5F683 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22648 (s : N.State) (i : N.Inputs) :
  R.v22648 (state s) (inputs i) = Zmod.unsigned (N.v22648 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22648 s i)) at 1.
  unfold R.v22648, N.v22648.
  unfold R.v6, N.v6.
  rewrite !state_r682_nr_5F682.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r682_nr_5F682 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22649 (s : N.State) (i : N.Inputs) :
  R.v22649 (state s) (inputs i) = Zmod.unsigned (N.v22649 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22649 s i)) at 1.
  unfold R.v22649, N.v22649.
  rewrite ?node_22647.
  rewrite ?node_22648.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22650 (s : N.State) (i : N.Inputs) :
  R.v22650 (state s) (inputs i) = Zmod.unsigned (N.v22650 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22650 s i)) at 1.
  unfold R.v22650, N.v22650.
  unfold R.v16484, N.v16484.
  rewrite ?node_22649.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22651 (s : N.State) (i : N.Inputs) :
  R.v22651 (state s) (inputs i) = Zmod.unsigned (N.v22651 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22651 s i)) at 1.
  unfold R.v22651, N.v22651.
  rewrite ?node_22646.
  rewrite ?node_22650.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22652 (s : N.State) (i : N.Inputs) :
  R.v22652 (state s) (inputs i) = Zmod.unsigned (N.v22652 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22652 s i)) at 1.
  unfold R.v22652, N.v22652.
  unfold R.v6, N.v6.
  rewrite ?node_22651.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22653 (s : N.State) (i : N.Inputs) :
  R.v22653 (state s) (inputs i) = Zmod.unsigned (N.v22653 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22653 s i)) at 1.
  unfold R.v22653, N.v22653.
  rewrite ?node_8189.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22654 (s : N.State) (i : N.Inputs) :
  R.v22654 (state s) (inputs i) = Zmod.unsigned (N.v22654 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22654 s i)) at 1.
  unfold R.v22654, N.v22654.
  unfold R.v6, N.v6.
  rewrite ?node_8315.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22655 (s : N.State) (i : N.Inputs) :
  R.v22655 (state s) (inputs i) = Zmod.unsigned (N.v22655 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22655 s i)) at 1.
  unfold R.v22655, N.v22655.
  rewrite ?node_22653.
  rewrite ?node_22654.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22656 (s : N.State) (i : N.Inputs) :
  R.v22656 (state s) (inputs i) = Zmod.unsigned (N.v22656 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22656 s i)) at 1.
  unfold R.v22656, N.v22656.
  rewrite ?node_22652.
  rewrite ?node_22655.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22657 (s : N.State) (i : N.Inputs) :
  R.v22657 (state s) (inputs i) = Zmod.unsigned (N.v22657 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22657 s i)) at 1.
  unfold R.v22657, N.v22657.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22658 (s : N.State) (i : N.Inputs) :
  R.v22658 (state s) (inputs i) = Zmod.unsigned (N.v22658 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22658 s i)) at 1.
  unfold R.v22658, N.v22658.
  rewrite ?node_8193.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22659 (s : N.State) (i : N.Inputs) :
  R.v22659 (state s) (inputs i) = Zmod.unsigned (N.v22659 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22659 s i)) at 1.
  unfold R.v22659, N.v22659.
  unfold R.v6, N.v6.
  rewrite !state_r685_nr_5F685.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r685_nr_5F685 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22660 (s : N.State) (i : N.Inputs) :
  R.v22660 (state s) (inputs i) = Zmod.unsigned (N.v22660 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22660 s i)) at 1.
  unfold R.v22660, N.v22660.
  unfold R.v6, N.v6.
  rewrite ?node_8189.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22661 (s : N.State) (i : N.Inputs) :
  R.v22661 (state s) (inputs i) = Zmod.unsigned (N.v22661 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22661 s i)) at 1.
  unfold R.v22661, N.v22661.
  rewrite ?node_22659.
  rewrite ?node_22660.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22662 (s : N.State) (i : N.Inputs) :
  R.v22662 (state s) (inputs i) = Zmod.unsigned (N.v22662 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22662 s i)) at 1.
  unfold R.v22662, N.v22662.
  unfold R.v16484, N.v16484.
  rewrite ?node_22661.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22663 (s : N.State) (i : N.Inputs) :
  R.v22663 (state s) (inputs i) = Zmod.unsigned (N.v22663 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22663 s i)) at 1.
  unfold R.v22663, N.v22663.
  rewrite ?node_22658.
  rewrite ?node_22662.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22664 (s : N.State) (i : N.Inputs) :
  R.v22664 (state s) (inputs i) = Zmod.unsigned (N.v22664 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22664 s i)) at 1.
  unfold R.v22664, N.v22664.
  unfold R.v6, N.v6.
  rewrite ?node_22663.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22665 (s : N.State) (i : N.Inputs) :
  R.v22665 (state s) (inputs i) = Zmod.unsigned (N.v22665 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22665 s i)) at 1.
  unfold R.v22665, N.v22665.
  rewrite ?node_8194.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22666 (s : N.State) (i : N.Inputs) :
  R.v22666 (state s) (inputs i) = Zmod.unsigned (N.v22666 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22666 s i)) at 1.
  unfold R.v22666, N.v22666.
  unfold R.v6, N.v6.
  rewrite ?node_8362.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22667 (s : N.State) (i : N.Inputs) :
  R.v22667 (state s) (inputs i) = Zmod.unsigned (N.v22667 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22667 s i)) at 1.
  unfold R.v22667, N.v22667.
  rewrite ?node_22665.
  rewrite ?node_22666.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22668 (s : N.State) (i : N.Inputs) :
  R.v22668 (state s) (inputs i) = Zmod.unsigned (N.v22668 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22668 s i)) at 1.
  unfold R.v22668, N.v22668.
  rewrite ?node_22664.
  rewrite ?node_22667.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22669 (s : N.State) (i : N.Inputs) :
  R.v22669 (state s) (inputs i) = Zmod.unsigned (N.v22669 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22669 s i)) at 1.
  unfold R.v22669, N.v22669.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22670 (s : N.State) (i : N.Inputs) :
  R.v22670 (state s) (inputs i) = Zmod.unsigned (N.v22670 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22670 s i)) at 1.
  unfold R.v22670, N.v22670.
  rewrite ?node_8201.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22671 (s : N.State) (i : N.Inputs) :
  R.v22671 (state s) (inputs i) = Zmod.unsigned (N.v22671 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22671 s i)) at 1.
  unfold R.v22671, N.v22671.
  unfold R.v16463, N.v16463.
  rewrite !state_r689_nr_5F689.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r689_nr_5F689 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22672 (s : N.State) (i : N.Inputs) :
  R.v22672 (state s) (inputs i) = Zmod.unsigned (N.v22672 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22672 s i)) at 1.
  unfold R.v22672, N.v22672.
  unfold R.v16463, N.v16463.
  rewrite !state_r688_nr_5F688.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r688_nr_5F688 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22673 (s : N.State) (i : N.Inputs) :
  R.v22673 (state s) (inputs i) = Zmod.unsigned (N.v22673 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22673 s i)) at 1.
  unfold R.v22673, N.v22673.
  unfold R.v6, N.v6.
  rewrite !state_r687_nr_5F687.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r687_nr_5F687 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22674 (s : N.State) (i : N.Inputs) :
  R.v22674 (state s) (inputs i) = Zmod.unsigned (N.v22674 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22674 s i)) at 1.
  unfold R.v22674, N.v22674.
  unfold R.v6, N.v6.
  rewrite !state_r686_nr_5F686.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r686_nr_5F686 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22675 (s : N.State) (i : N.Inputs) :
  R.v22675 (state s) (inputs i) = Zmod.unsigned (N.v22675 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22675 s i)) at 1.
  unfold R.v22675, N.v22675.
  rewrite ?node_22673.
  rewrite ?node_22674.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22676 (s : N.State) (i : N.Inputs) :
  R.v22676 (state s) (inputs i) = Zmod.unsigned (N.v22676 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22676 s i)) at 1.
  unfold R.v22676, N.v22676.
  unfold R.v16484, N.v16484.
  rewrite ?node_22675.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22677 (s : N.State) (i : N.Inputs) :
  R.v22677 (state s) (inputs i) = Zmod.unsigned (N.v22677 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22677 s i)) at 1.
  unfold R.v22677, N.v22677.
  rewrite ?node_22670.
  rewrite ?node_22671.
  rewrite ?node_22672.
  rewrite ?node_22676.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22678 (s : N.State) (i : N.Inputs) :
  R.v22678 (state s) (inputs i) = Zmod.unsigned (N.v22678 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22678 s i)) at 1.
  unfold R.v22678, N.v22678.
  unfold R.v6, N.v6.
  rewrite ?node_22677.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22679 (s : N.State) (i : N.Inputs) :
  R.v22679 (state s) (inputs i) = Zmod.unsigned (N.v22679 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22679 s i)) at 1.
  unfold R.v22679, N.v22679.
  rewrite ?node_8202.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22680 (s : N.State) (i : N.Inputs) :
  R.v22680 (state s) (inputs i) = Zmod.unsigned (N.v22680 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22680 s i)) at 1.
  unfold R.v22680, N.v22680.
  unfold R.v6, N.v6.
  rewrite ?node_8323.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22681 (s : N.State) (i : N.Inputs) :
  R.v22681 (state s) (inputs i) = Zmod.unsigned (N.v22681 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22681 s i)) at 1.
  unfold R.v22681, N.v22681.
  unfold R.v6, N.v6.
  rewrite ?node_8366.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22682 (s : N.State) (i : N.Inputs) :
  R.v22682 (state s) (inputs i) = Zmod.unsigned (N.v22682 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22682 s i)) at 1.
  unfold R.v22682, N.v22682.
  rewrite ?node_22679.
  rewrite ?node_22680.
  rewrite ?node_22681.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22683 (s : N.State) (i : N.Inputs) :
  R.v22683 (state s) (inputs i) = Zmod.unsigned (N.v22683 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22683 s i)) at 1.
  unfold R.v22683, N.v22683.
  rewrite ?node_22678.
  rewrite ?node_22682.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22684 (s : N.State) (i : N.Inputs) :
  R.v22684 (state s) (inputs i) = Zmod.unsigned (N.v22684 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22684 s i)) at 1.
  unfold R.v22684, N.v22684.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22685 (s : N.State) (i : N.Inputs) :
  R.v22685 (state s) (inputs i) = Zmod.unsigned (N.v22685 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22685 s i)) at 1.
  unfold R.v22685, N.v22685.
  unfold R.v16463, N.v16463.
  rewrite !state_r688_nr_5F688.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r688_nr_5F688 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22686 (s : N.State) (i : N.Inputs) :
  R.v22686 (state s) (inputs i) = Zmod.unsigned (N.v22686 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22686 s i)) at 1.
  unfold R.v22686, N.v22686.
  unfold R.v6, N.v6.
  rewrite !state_r687_nr_5F687.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r687_nr_5F687 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22687 (s : N.State) (i : N.Inputs) :
  R.v22687 (state s) (inputs i) = Zmod.unsigned (N.v22687 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22687 s i)) at 1.
  unfold R.v22687, N.v22687.
  unfold R.v6, N.v6.
  rewrite !state_r686_nr_5F686.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r686_nr_5F686 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22688 (s : N.State) (i : N.Inputs) :
  R.v22688 (state s) (inputs i) = Zmod.unsigned (N.v22688 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22688 s i)) at 1.
  unfold R.v22688, N.v22688.
  rewrite ?node_22686.
  rewrite ?node_22687.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22689 (s : N.State) (i : N.Inputs) :
  R.v22689 (state s) (inputs i) = Zmod.unsigned (N.v22689 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22689 s i)) at 1.
  unfold R.v22689, N.v22689.
  unfold R.v16484, N.v16484.
  rewrite ?node_22688.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22690 (s : N.State) (i : N.Inputs) :
  R.v22690 (state s) (inputs i) = Zmod.unsigned (N.v22690 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22690 s i)) at 1.
  unfold R.v22690, N.v22690.
  rewrite ?node_22685.
  rewrite ?node_22689.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22691 (s : N.State) (i : N.Inputs) :
  R.v22691 (state s) (inputs i) = Zmod.unsigned (N.v22691 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22691 s i)) at 1.
  unfold R.v22691, N.v22691.
  unfold R.v6, N.v6.
  rewrite ?node_22690.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22692 (s : N.State) (i : N.Inputs) :
  R.v22692 (state s) (inputs i) = Zmod.unsigned (N.v22692 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22692 s i)) at 1.
  unfold R.v22692, N.v22692.
  rewrite ?node_8197.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22693 (s : N.State) (i : N.Inputs) :
  R.v22693 (state s) (inputs i) = Zmod.unsigned (N.v22693 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22693 s i)) at 1.
  unfold R.v22693, N.v22693.
  unfold R.v6, N.v6.
  rewrite ?node_8323.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22694 (s : N.State) (i : N.Inputs) :
  R.v22694 (state s) (inputs i) = Zmod.unsigned (N.v22694 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22694 s i)) at 1.
  unfold R.v22694, N.v22694.
  rewrite ?node_22692.
  rewrite ?node_22693.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22695 (s : N.State) (i : N.Inputs) :
  R.v22695 (state s) (inputs i) = Zmod.unsigned (N.v22695 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22695 s i)) at 1.
  unfold R.v22695, N.v22695.
  rewrite ?node_22691.
  rewrite ?node_22694.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22696 (s : N.State) (i : N.Inputs) :
  R.v22696 (state s) (inputs i) = Zmod.unsigned (N.v22696 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22696 s i)) at 1.
  unfold R.v22696, N.v22696.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22697 (s : N.State) (i : N.Inputs) :
  R.v22697 (state s) (inputs i) = Zmod.unsigned (N.v22697 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22697 s i)) at 1.
  unfold R.v22697, N.v22697.
  rewrite ?node_8201.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22698 (s : N.State) (i : N.Inputs) :
  R.v22698 (state s) (inputs i) = Zmod.unsigned (N.v22698 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22698 s i)) at 1.
  unfold R.v22698, N.v22698.
  unfold R.v6, N.v6.
  rewrite !state_r689_nr_5F689.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r689_nr_5F689 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22699 (s : N.State) (i : N.Inputs) :
  R.v22699 (state s) (inputs i) = Zmod.unsigned (N.v22699 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22699 s i)) at 1.
  unfold R.v22699, N.v22699.
  unfold R.v6, N.v6.
  rewrite ?node_8197.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22700 (s : N.State) (i : N.Inputs) :
  R.v22700 (state s) (inputs i) = Zmod.unsigned (N.v22700 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22700 s i)) at 1.
  unfold R.v22700, N.v22700.
  rewrite ?node_22698.
  rewrite ?node_22699.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22701 (s : N.State) (i : N.Inputs) :
  R.v22701 (state s) (inputs i) = Zmod.unsigned (N.v22701 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22701 s i)) at 1.
  unfold R.v22701, N.v22701.
  unfold R.v16484, N.v16484.
  rewrite ?node_22700.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22702 (s : N.State) (i : N.Inputs) :
  R.v22702 (state s) (inputs i) = Zmod.unsigned (N.v22702 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22702 s i)) at 1.
  unfold R.v22702, N.v22702.
  rewrite ?node_22697.
  rewrite ?node_22701.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22703 (s : N.State) (i : N.Inputs) :
  R.v22703 (state s) (inputs i) = Zmod.unsigned (N.v22703 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22703 s i)) at 1.
  unfold R.v22703, N.v22703.
  unfold R.v6, N.v6.
  rewrite ?node_22702.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22704 (s : N.State) (i : N.Inputs) :
  R.v22704 (state s) (inputs i) = Zmod.unsigned (N.v22704 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22704 s i)) at 1.
  unfold R.v22704, N.v22704.
  rewrite ?node_8202.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22705 (s : N.State) (i : N.Inputs) :
  R.v22705 (state s) (inputs i) = Zmod.unsigned (N.v22705 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22705 s i)) at 1.
  unfold R.v22705, N.v22705.
  unfold R.v6, N.v6.
  rewrite ?node_8366.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22706 (s : N.State) (i : N.Inputs) :
  R.v22706 (state s) (inputs i) = Zmod.unsigned (N.v22706 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22706 s i)) at 1.
  unfold R.v22706, N.v22706.
  rewrite ?node_22704.
  rewrite ?node_22705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22707 (s : N.State) (i : N.Inputs) :
  R.v22707 (state s) (inputs i) = Zmod.unsigned (N.v22707 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22707 s i)) at 1.
  unfold R.v22707, N.v22707.
  rewrite ?node_22703.
  rewrite ?node_22706.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22708 (s : N.State) (i : N.Inputs) :
  R.v22708 (state s) (inputs i) = Zmod.unsigned (N.v22708 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22708 s i)) at 1.
  unfold R.v22708, N.v22708.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22709 (s : N.State) (i : N.Inputs) :
  R.v22709 (state s) (inputs i) = Zmod.unsigned (N.v22709 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22709 s i)) at 1.
  unfold R.v22709, N.v22709.
  rewrite ?node_8213.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22710 (s : N.State) (i : N.Inputs) :
  R.v22710 (state s) (inputs i) = Zmod.unsigned (N.v22710 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22710 s i)) at 1.
  unfold R.v22710, N.v22710.
  unfold R.v16463, N.v16463.
  rewrite !state_r693_nr_5F693.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r693_nr_5F693 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22711 (s : N.State) (i : N.Inputs) :
  R.v22711 (state s) (inputs i) = Zmod.unsigned (N.v22711 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22711 s i)) at 1.
  unfold R.v22711, N.v22711.
  unfold R.v16463, N.v16463.
  rewrite !state_r692_nr_5F692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r692_nr_5F692 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22712 (s : N.State) (i : N.Inputs) :
  R.v22712 (state s) (inputs i) = Zmod.unsigned (N.v22712 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22712 s i)) at 1.
  unfold R.v22712, N.v22712.
  unfold R.v6, N.v6.
  rewrite !state_r691_nr_5F691.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r691_nr_5F691 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22713 (s : N.State) (i : N.Inputs) :
  R.v22713 (state s) (inputs i) = Zmod.unsigned (N.v22713 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22713 s i)) at 1.
  unfold R.v22713, N.v22713.
  unfold R.v6, N.v6.
  rewrite !state_r690_nr_5F690.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r690_nr_5F690 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22714 (s : N.State) (i : N.Inputs) :
  R.v22714 (state s) (inputs i) = Zmod.unsigned (N.v22714 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22714 s i)) at 1.
  unfold R.v22714, N.v22714.
  rewrite ?node_22712.
  rewrite ?node_22713.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22715 (s : N.State) (i : N.Inputs) :
  R.v22715 (state s) (inputs i) = Zmod.unsigned (N.v22715 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22715 s i)) at 1.
  unfold R.v22715, N.v22715.
  unfold R.v16484, N.v16484.
  rewrite ?node_22714.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22716 (s : N.State) (i : N.Inputs) :
  R.v22716 (state s) (inputs i) = Zmod.unsigned (N.v22716 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22716 s i)) at 1.
  unfold R.v22716, N.v22716.
  rewrite ?node_22709.
  rewrite ?node_22710.
  rewrite ?node_22711.
  rewrite ?node_22715.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22717 (s : N.State) (i : N.Inputs) :
  R.v22717 (state s) (inputs i) = Zmod.unsigned (N.v22717 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22717 s i)) at 1.
  unfold R.v22717, N.v22717.
  unfold R.v6, N.v6.
  rewrite ?node_22716.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22718 (s : N.State) (i : N.Inputs) :
  R.v22718 (state s) (inputs i) = Zmod.unsigned (N.v22718 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22718 s i)) at 1.
  unfold R.v22718, N.v22718.
  rewrite ?node_8214.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22719 (s : N.State) (i : N.Inputs) :
  R.v22719 (state s) (inputs i) = Zmod.unsigned (N.v22719 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22719 s i)) at 1.
  unfold R.v22719, N.v22719.
  unfold R.v6, N.v6.
  rewrite ?node_8335.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22720 (s : N.State) (i : N.Inputs) :
  R.v22720 (state s) (inputs i) = Zmod.unsigned (N.v22720 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22720 s i)) at 1.
  unfold R.v22720, N.v22720.
  unfold R.v6, N.v6.
  rewrite ?node_8370.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22721 (s : N.State) (i : N.Inputs) :
  R.v22721 (state s) (inputs i) = Zmod.unsigned (N.v22721 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22721 s i)) at 1.
  unfold R.v22721, N.v22721.
  rewrite ?node_22718.
  rewrite ?node_22719.
  rewrite ?node_22720.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22722 (s : N.State) (i : N.Inputs) :
  R.v22722 (state s) (inputs i) = Zmod.unsigned (N.v22722 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22722 s i)) at 1.
  unfold R.v22722, N.v22722.
  rewrite ?node_22717.
  rewrite ?node_22721.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22723 (s : N.State) (i : N.Inputs) :
  R.v22723 (state s) (inputs i) = Zmod.unsigned (N.v22723 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22723 s i)) at 1.
  unfold R.v22723, N.v22723.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22724 (s : N.State) (i : N.Inputs) :
  R.v22724 (state s) (inputs i) = Zmod.unsigned (N.v22724 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22724 s i)) at 1.
  unfold R.v22724, N.v22724.
  unfold R.v16463, N.v16463.
  rewrite !state_r692_nr_5F692.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r692_nr_5F692 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22725 (s : N.State) (i : N.Inputs) :
  R.v22725 (state s) (inputs i) = Zmod.unsigned (N.v22725 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22725 s i)) at 1.
  unfold R.v22725, N.v22725.
  unfold R.v6, N.v6.
  rewrite !state_r691_nr_5F691.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r691_nr_5F691 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22726 (s : N.State) (i : N.Inputs) :
  R.v22726 (state s) (inputs i) = Zmod.unsigned (N.v22726 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22726 s i)) at 1.
  unfold R.v22726, N.v22726.
  unfold R.v6, N.v6.
  rewrite !state_r690_nr_5F690.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r690_nr_5F690 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22727 (s : N.State) (i : N.Inputs) :
  R.v22727 (state s) (inputs i) = Zmod.unsigned (N.v22727 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22727 s i)) at 1.
  unfold R.v22727, N.v22727.
  rewrite ?node_22725.
  rewrite ?node_22726.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22728 (s : N.State) (i : N.Inputs) :
  R.v22728 (state s) (inputs i) = Zmod.unsigned (N.v22728 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22728 s i)) at 1.
  unfold R.v22728, N.v22728.
  unfold R.v16484, N.v16484.
  rewrite ?node_22727.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22729 (s : N.State) (i : N.Inputs) :
  R.v22729 (state s) (inputs i) = Zmod.unsigned (N.v22729 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22729 s i)) at 1.
  unfold R.v22729, N.v22729.
  rewrite ?node_22724.
  rewrite ?node_22728.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22730 (s : N.State) (i : N.Inputs) :
  R.v22730 (state s) (inputs i) = Zmod.unsigned (N.v22730 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22730 s i)) at 1.
  unfold R.v22730, N.v22730.
  unfold R.v6, N.v6.
  rewrite ?node_22729.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22731 (s : N.State) (i : N.Inputs) :
  R.v22731 (state s) (inputs i) = Zmod.unsigned (N.v22731 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22731 s i)) at 1.
  unfold R.v22731, N.v22731.
  rewrite ?node_8209.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22732 (s : N.State) (i : N.Inputs) :
  R.v22732 (state s) (inputs i) = Zmod.unsigned (N.v22732 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22732 s i)) at 1.
  unfold R.v22732, N.v22732.
  unfold R.v6, N.v6.
  rewrite ?node_8335.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22733 (s : N.State) (i : N.Inputs) :
  R.v22733 (state s) (inputs i) = Zmod.unsigned (N.v22733 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22733 s i)) at 1.
  unfold R.v22733, N.v22733.
  rewrite ?node_22731.
  rewrite ?node_22732.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22734 (s : N.State) (i : N.Inputs) :
  R.v22734 (state s) (inputs i) = Zmod.unsigned (N.v22734 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22734 s i)) at 1.
  unfold R.v22734, N.v22734.
  rewrite ?node_22730.
  rewrite ?node_22733.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22735 (s : N.State) (i : N.Inputs) :
  R.v22735 (state s) (inputs i) = Zmod.unsigned (N.v22735 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22735 s i)) at 1.
  unfold R.v22735, N.v22735.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22736 (s : N.State) (i : N.Inputs) :
  R.v22736 (state s) (inputs i) = Zmod.unsigned (N.v22736 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22736 s i)) at 1.
  unfold R.v22736, N.v22736.
  rewrite ?node_8213.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22737 (s : N.State) (i : N.Inputs) :
  R.v22737 (state s) (inputs i) = Zmod.unsigned (N.v22737 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22737 s i)) at 1.
  unfold R.v22737, N.v22737.
  unfold R.v6, N.v6.
  rewrite !state_r693_nr_5F693.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r693_nr_5F693 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22738 (s : N.State) (i : N.Inputs) :
  R.v22738 (state s) (inputs i) = Zmod.unsigned (N.v22738 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22738 s i)) at 1.
  unfold R.v22738, N.v22738.
  unfold R.v6, N.v6.
  rewrite ?node_8209.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22739 (s : N.State) (i : N.Inputs) :
  R.v22739 (state s) (inputs i) = Zmod.unsigned (N.v22739 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22739 s i)) at 1.
  unfold R.v22739, N.v22739.
  rewrite ?node_22737.
  rewrite ?node_22738.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22740 (s : N.State) (i : N.Inputs) :
  R.v22740 (state s) (inputs i) = Zmod.unsigned (N.v22740 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22740 s i)) at 1.
  unfold R.v22740, N.v22740.
  unfold R.v16484, N.v16484.
  rewrite ?node_22739.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22741 (s : N.State) (i : N.Inputs) :
  R.v22741 (state s) (inputs i) = Zmod.unsigned (N.v22741 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22741 s i)) at 1.
  unfold R.v22741, N.v22741.
  rewrite ?node_22736.
  rewrite ?node_22740.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22742 (s : N.State) (i : N.Inputs) :
  R.v22742 (state s) (inputs i) = Zmod.unsigned (N.v22742 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22742 s i)) at 1.
  unfold R.v22742, N.v22742.
  unfold R.v6, N.v6.
  rewrite ?node_22741.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22743 (s : N.State) (i : N.Inputs) :
  R.v22743 (state s) (inputs i) = Zmod.unsigned (N.v22743 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22743 s i)) at 1.
  unfold R.v22743, N.v22743.
  rewrite ?node_8214.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22744 (s : N.State) (i : N.Inputs) :
  R.v22744 (state s) (inputs i) = Zmod.unsigned (N.v22744 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22744 s i)) at 1.
  unfold R.v22744, N.v22744.
  unfold R.v6, N.v6.
  rewrite ?node_8370.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22745 (s : N.State) (i : N.Inputs) :
  R.v22745 (state s) (inputs i) = Zmod.unsigned (N.v22745 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22745 s i)) at 1.
  unfold R.v22745, N.v22745.
  rewrite ?node_22743.
  rewrite ?node_22744.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22746 (s : N.State) (i : N.Inputs) :
  R.v22746 (state s) (inputs i) = Zmod.unsigned (N.v22746 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22746 s i)) at 1.
  unfold R.v22746, N.v22746.
  rewrite ?node_22742.
  rewrite ?node_22745.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22747 (s : N.State) (i : N.Inputs) :
  R.v22747 (state s) (inputs i) = Zmod.unsigned (N.v22747 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22747 s i)) at 1.
  unfold R.v22747, N.v22747.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22748 (s : N.State) (i : N.Inputs) :
  R.v22748 (state s) (inputs i) = Zmod.unsigned (N.v22748 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22748 s i)) at 1.
  unfold R.v22748, N.v22748.
  rewrite ?node_8220.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22749 (s : N.State) (i : N.Inputs) :
  R.v22749 (state s) (inputs i) = Zmod.unsigned (N.v22749 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22749 s i)) at 1.
  unfold R.v22749, N.v22749.
  unfold R.v16463, N.v16463.
  rewrite !state_r697_nr_5F697.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r697_nr_5F697 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22750 (s : N.State) (i : N.Inputs) :
  R.v22750 (state s) (inputs i) = Zmod.unsigned (N.v22750 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22750 s i)) at 1.
  unfold R.v22750, N.v22750.
  unfold R.v16463, N.v16463.
  rewrite !state_r696_nr_5F696.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r696_nr_5F696 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22751 (s : N.State) (i : N.Inputs) :
  R.v22751 (state s) (inputs i) = Zmod.unsigned (N.v22751 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22751 s i)) at 1.
  unfold R.v22751, N.v22751.
  unfold R.v6, N.v6.
  rewrite !state_r695_nr_5F695.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r695_nr_5F695 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22752 (s : N.State) (i : N.Inputs) :
  R.v22752 (state s) (inputs i) = Zmod.unsigned (N.v22752 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22752 s i)) at 1.
  unfold R.v22752, N.v22752.
  unfold R.v6, N.v6.
  rewrite !state_r694_nr_5F694.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r694_nr_5F694 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22753 (s : N.State) (i : N.Inputs) :
  R.v22753 (state s) (inputs i) = Zmod.unsigned (N.v22753 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22753 s i)) at 1.
  unfold R.v22753, N.v22753.
  rewrite ?node_22751.
  rewrite ?node_22752.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22754 (s : N.State) (i : N.Inputs) :
  R.v22754 (state s) (inputs i) = Zmod.unsigned (N.v22754 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22754 s i)) at 1.
  unfold R.v22754, N.v22754.
  unfold R.v16484, N.v16484.
  rewrite ?node_22753.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22755 (s : N.State) (i : N.Inputs) :
  R.v22755 (state s) (inputs i) = Zmod.unsigned (N.v22755 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22755 s i)) at 1.
  unfold R.v22755, N.v22755.
  rewrite ?node_22748.
  rewrite ?node_22749.
  rewrite ?node_22750.
  rewrite ?node_22754.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22756 (s : N.State) (i : N.Inputs) :
  R.v22756 (state s) (inputs i) = Zmod.unsigned (N.v22756 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22756 s i)) at 1.
  unfold R.v22756, N.v22756.
  unfold R.v6, N.v6.
  rewrite ?node_22755.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22757 (s : N.State) (i : N.Inputs) :
  R.v22757 (state s) (inputs i) = Zmod.unsigned (N.v22757 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22757 s i)) at 1.
  unfold R.v22757, N.v22757.
  rewrite ?node_8221.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22758 (s : N.State) (i : N.Inputs) :
  R.v22758 (state s) (inputs i) = Zmod.unsigned (N.v22758 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22758 s i)) at 1.
  unfold R.v22758, N.v22758.
  unfold R.v6, N.v6.
  rewrite ?node_8342.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22759 (s : N.State) (i : N.Inputs) :
  R.v22759 (state s) (inputs i) = Zmod.unsigned (N.v22759 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22759 s i)) at 1.
  unfold R.v22759, N.v22759.
  unfold R.v6, N.v6.
  rewrite ?node_8379.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22760 (s : N.State) (i : N.Inputs) :
  R.v22760 (state s) (inputs i) = Zmod.unsigned (N.v22760 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22760 s i)) at 1.
  unfold R.v22760, N.v22760.
  rewrite ?node_22757.
  rewrite ?node_22758.
  rewrite ?node_22759.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22761 (s : N.State) (i : N.Inputs) :
  R.v22761 (state s) (inputs i) = Zmod.unsigned (N.v22761 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22761 s i)) at 1.
  unfold R.v22761, N.v22761.
  rewrite ?node_22756.
  rewrite ?node_22760.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22762 (s : N.State) (i : N.Inputs) :
  R.v22762 (state s) (inputs i) = Zmod.unsigned (N.v22762 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22762 s i)) at 1.
  unfold R.v22762, N.v22762.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22763 (s : N.State) (i : N.Inputs) :
  R.v22763 (state s) (inputs i) = Zmod.unsigned (N.v22763 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22763 s i)) at 1.
  unfold R.v22763, N.v22763.
  unfold R.v16463, N.v16463.
  rewrite !state_r696_nr_5F696.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r696_nr_5F696 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22764 (s : N.State) (i : N.Inputs) :
  R.v22764 (state s) (inputs i) = Zmod.unsigned (N.v22764 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22764 s i)) at 1.
  unfold R.v22764, N.v22764.
  unfold R.v6, N.v6.
  rewrite !state_r695_nr_5F695.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r695_nr_5F695 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22765 (s : N.State) (i : N.Inputs) :
  R.v22765 (state s) (inputs i) = Zmod.unsigned (N.v22765 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22765 s i)) at 1.
  unfold R.v22765, N.v22765.
  unfold R.v6, N.v6.
  rewrite !state_r694_nr_5F694.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r694_nr_5F694 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22766 (s : N.State) (i : N.Inputs) :
  R.v22766 (state s) (inputs i) = Zmod.unsigned (N.v22766 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22766 s i)) at 1.
  unfold R.v22766, N.v22766.
  rewrite ?node_22764.
  rewrite ?node_22765.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22767 (s : N.State) (i : N.Inputs) :
  R.v22767 (state s) (inputs i) = Zmod.unsigned (N.v22767 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22767 s i)) at 1.
  unfold R.v22767, N.v22767.
  unfold R.v16484, N.v16484.
  rewrite ?node_22766.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22768 (s : N.State) (i : N.Inputs) :
  R.v22768 (state s) (inputs i) = Zmod.unsigned (N.v22768 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22768 s i)) at 1.
  unfold R.v22768, N.v22768.
  rewrite ?node_22763.
  rewrite ?node_22767.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22769 (s : N.State) (i : N.Inputs) :
  R.v22769 (state s) (inputs i) = Zmod.unsigned (N.v22769 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22769 s i)) at 1.
  unfold R.v22769, N.v22769.
  unfold R.v6, N.v6.
  rewrite ?node_22768.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22770 (s : N.State) (i : N.Inputs) :
  R.v22770 (state s) (inputs i) = Zmod.unsigned (N.v22770 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22770 s i)) at 1.
  unfold R.v22770, N.v22770.
  rewrite ?node_8216.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22771 (s : N.State) (i : N.Inputs) :
  R.v22771 (state s) (inputs i) = Zmod.unsigned (N.v22771 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22771 s i)) at 1.
  unfold R.v22771, N.v22771.
  unfold R.v6, N.v6.
  rewrite ?node_8342.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22772 (s : N.State) (i : N.Inputs) :
  R.v22772 (state s) (inputs i) = Zmod.unsigned (N.v22772 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22772 s i)) at 1.
  unfold R.v22772, N.v22772.
  rewrite ?node_22770.
  rewrite ?node_22771.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22773 (s : N.State) (i : N.Inputs) :
  R.v22773 (state s) (inputs i) = Zmod.unsigned (N.v22773 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22773 s i)) at 1.
  unfold R.v22773, N.v22773.
  rewrite ?node_22769.
  rewrite ?node_22772.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22774 (s : N.State) (i : N.Inputs) :
  R.v22774 (state s) (inputs i) = Zmod.unsigned (N.v22774 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22774 s i)) at 1.
  unfold R.v22774, N.v22774.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22775 (s : N.State) (i : N.Inputs) :
  R.v22775 (state s) (inputs i) = Zmod.unsigned (N.v22775 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22775 s i)) at 1.
  unfold R.v22775, N.v22775.
  rewrite ?node_8220.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22776 (s : N.State) (i : N.Inputs) :
  R.v22776 (state s) (inputs i) = Zmod.unsigned (N.v22776 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22776 s i)) at 1.
  unfold R.v22776, N.v22776.
  unfold R.v6, N.v6.
  rewrite !state_r697_nr_5F697.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r697_nr_5F697 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22777 (s : N.State) (i : N.Inputs) :
  R.v22777 (state s) (inputs i) = Zmod.unsigned (N.v22777 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22777 s i)) at 1.
  unfold R.v22777, N.v22777.
  unfold R.v6, N.v6.
  rewrite ?node_8216.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22778 (s : N.State) (i : N.Inputs) :
  R.v22778 (state s) (inputs i) = Zmod.unsigned (N.v22778 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22778 s i)) at 1.
  unfold R.v22778, N.v22778.
  rewrite ?node_22776.
  rewrite ?node_22777.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22779 (s : N.State) (i : N.Inputs) :
  R.v22779 (state s) (inputs i) = Zmod.unsigned (N.v22779 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22779 s i)) at 1.
  unfold R.v22779, N.v22779.
  unfold R.v16484, N.v16484.
  rewrite ?node_22778.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22780 (s : N.State) (i : N.Inputs) :
  R.v22780 (state s) (inputs i) = Zmod.unsigned (N.v22780 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22780 s i)) at 1.
  unfold R.v22780, N.v22780.
  rewrite ?node_22775.
  rewrite ?node_22779.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22781 (s : N.State) (i : N.Inputs) :
  R.v22781 (state s) (inputs i) = Zmod.unsigned (N.v22781 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22781 s i)) at 1.
  unfold R.v22781, N.v22781.
  unfold R.v6, N.v6.
  rewrite ?node_22780.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22782 (s : N.State) (i : N.Inputs) :
  R.v22782 (state s) (inputs i) = Zmod.unsigned (N.v22782 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22782 s i)) at 1.
  unfold R.v22782, N.v22782.
  rewrite ?node_8221.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22783 (s : N.State) (i : N.Inputs) :
  R.v22783 (state s) (inputs i) = Zmod.unsigned (N.v22783 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22783 s i)) at 1.
  unfold R.v22783, N.v22783.
  unfold R.v6, N.v6.
  rewrite ?node_8379.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22784 (s : N.State) (i : N.Inputs) :
  R.v22784 (state s) (inputs i) = Zmod.unsigned (N.v22784 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22784 s i)) at 1.
  unfold R.v22784, N.v22784.
  rewrite ?node_22782.
  rewrite ?node_22783.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22785 (s : N.State) (i : N.Inputs) :
  R.v22785 (state s) (inputs i) = Zmod.unsigned (N.v22785 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22785 s i)) at 1.
  unfold R.v22785, N.v22785.
  rewrite ?node_22781.
  rewrite ?node_22784.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22786 (s : N.State) (i : N.Inputs) :
  R.v22786 (state s) (inputs i) = Zmod.unsigned (N.v22786 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22786 s i)) at 1.
  unfold R.v22786, N.v22786.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22787 (s : N.State) (i : N.Inputs) :
  R.v22787 (state s) (inputs i) = Zmod.unsigned (N.v22787 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22787 s i)) at 1.
  unfold R.v22787, N.v22787.
  unfold R.v6, N.v6.
  rewrite !state_r699_nr_5F699.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r699_nr_5F699 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22788 (s : N.State) (i : N.Inputs) :
  R.v22788 (state s) (inputs i) = Zmod.unsigned (N.v22788 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22788 s i)) at 1.
  unfold R.v22788, N.v22788.
  unfold R.v6, N.v6.
  rewrite !state_r698_nr_5F698.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r698_nr_5F698 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22789 (s : N.State) (i : N.Inputs) :
  R.v22789 (state s) (inputs i) = Zmod.unsigned (N.v22789 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22789 s i)) at 1.
  unfold R.v22789, N.v22789.
  rewrite ?node_22787.
  rewrite ?node_22788.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22790 (s : N.State) (i : N.Inputs) :
  R.v22790 (state s) (inputs i) = Zmod.unsigned (N.v22790 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22790 s i)) at 1.
  unfold R.v22790, N.v22790.
  unfold R.v16463, N.v16463.
  rewrite ?node_22789.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22791 (s : N.State) (i : N.Inputs) :
  R.v22791 (state s) (inputs i) = Zmod.unsigned (N.v22791 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22791 s i)) at 1.
  unfold R.v22791, N.v22791.
  rewrite ?node_8223.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22792 (s : N.State) (i : N.Inputs) :
  R.v22792 (state s) (inputs i) = Zmod.unsigned (N.v22792 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22792 s i)) at 1.
  unfold R.v22792, N.v22792.
  unfold R.v6, N.v6.
  rewrite ?node_8380.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22793 (s : N.State) (i : N.Inputs) :
  R.v22793 (state s) (inputs i) = Zmod.unsigned (N.v22793 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22793 s i)) at 1.
  unfold R.v22793, N.v22793.
  rewrite ?node_22791.
  rewrite ?node_22792.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22794 (s : N.State) (i : N.Inputs) :
  R.v22794 (state s) (inputs i) = Zmod.unsigned (N.v22794 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22794 s i)) at 1.
  unfold R.v22794, N.v22794.
  rewrite ?node_22790.
  rewrite ?node_22793.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22795 (s : N.State) (i : N.Inputs) :
  R.v22795 (state s) (inputs i) = Zmod.unsigned (N.v22795 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22795 s i)) at 1.
  unfold R.v22795, N.v22795.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22796 (s : N.State) (i : N.Inputs) :
  R.v22796 (state s) (inputs i) = Zmod.unsigned (N.v22796 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22796 s i)) at 1.
  unfold R.v22796, N.v22796.
  rewrite ?node_8300.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22797 (s : N.State) (i : N.Inputs) :
  R.v22797 (state s) (inputs i) = Zmod.unsigned (N.v22797 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22797 s i)) at 1.
  unfold R.v22797, N.v22797.
  unfold R.v16463, N.v16463.
  rewrite !state_r703_nr_5F703.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r703_nr_5F703 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22798 (s : N.State) (i : N.Inputs) :
  R.v22798 (state s) (inputs i) = Zmod.unsigned (N.v22798 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22798 s i)) at 1.
  unfold R.v22798, N.v22798.
  unfold R.v16463, N.v16463.
  rewrite !state_r702_nr_5F702.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r702_nr_5F702 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22799 (s : N.State) (i : N.Inputs) :
  R.v22799 (state s) (inputs i) = Zmod.unsigned (N.v22799 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22799 s i)) at 1.
  unfold R.v22799, N.v22799.
  unfold R.v6, N.v6.
  rewrite !state_r701_nr_5F701.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r701_nr_5F701 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22800 (s : N.State) (i : N.Inputs) :
  R.v22800 (state s) (inputs i) = Zmod.unsigned (N.v22800 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22800 s i)) at 1.
  unfold R.v22800, N.v22800.
  unfold R.v6, N.v6.
  rewrite !state_r700_nr_5F700.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r700_nr_5F700 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22801 (s : N.State) (i : N.Inputs) :
  R.v22801 (state s) (inputs i) = Zmod.unsigned (N.v22801 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22801 s i)) at 1.
  unfold R.v22801, N.v22801.
  rewrite ?node_22799.
  rewrite ?node_22800.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22802 (s : N.State) (i : N.Inputs) :
  R.v22802 (state s) (inputs i) = Zmod.unsigned (N.v22802 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22802 s i)) at 1.
  unfold R.v22802, N.v22802.
  unfold R.v16484, N.v16484.
  rewrite ?node_22801.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22803 (s : N.State) (i : N.Inputs) :
  R.v22803 (state s) (inputs i) = Zmod.unsigned (N.v22803 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22803 s i)) at 1.
  unfold R.v22803, N.v22803.
  rewrite ?node_22796.
  rewrite ?node_22797.
  rewrite ?node_22798.
  rewrite ?node_22802.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22804 (s : N.State) (i : N.Inputs) :
  R.v22804 (state s) (inputs i) = Zmod.unsigned (N.v22804 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22804 s i)) at 1.
  unfold R.v22804, N.v22804.
  unfold R.v6, N.v6.
  rewrite ?node_22803.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22805 (s : N.State) (i : N.Inputs) :
  R.v22805 (state s) (inputs i) = Zmod.unsigned (N.v22805 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22805 s i)) at 1.
  unfold R.v22805, N.v22805.
  rewrite ?node_8301.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22806 (s : N.State) (i : N.Inputs) :
  R.v22806 (state s) (inputs i) = Zmod.unsigned (N.v22806 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22806 s i)) at 1.
  unfold R.v22806, N.v22806.
  unfold R.v6, N.v6.
  rewrite ?node_8425.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22807 (s : N.State) (i : N.Inputs) :
  R.v22807 (state s) (inputs i) = Zmod.unsigned (N.v22807 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22807 s i)) at 1.
  unfold R.v22807, N.v22807.
  unfold R.v6, N.v6.
  rewrite ?node_8475.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22808 (s : N.State) (i : N.Inputs) :
  R.v22808 (state s) (inputs i) = Zmod.unsigned (N.v22808 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22808 s i)) at 1.
  unfold R.v22808, N.v22808.
  rewrite ?node_22805.
  rewrite ?node_22806.
  rewrite ?node_22807.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22809 (s : N.State) (i : N.Inputs) :
  R.v22809 (state s) (inputs i) = Zmod.unsigned (N.v22809 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22809 s i)) at 1.
  unfold R.v22809, N.v22809.
  rewrite ?node_22804.
  rewrite ?node_22808.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22810 (s : N.State) (i : N.Inputs) :
  R.v22810 (state s) (inputs i) = Zmod.unsigned (N.v22810 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22810 s i)) at 1.
  unfold R.v22810, N.v22810.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22811 (s : N.State) (i : N.Inputs) :
  R.v22811 (state s) (inputs i) = Zmod.unsigned (N.v22811 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22811 s i)) at 1.
  unfold R.v22811, N.v22811.
  unfold R.v16463, N.v16463.
  rewrite !state_r702_nr_5F702.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r702_nr_5F702 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22812 (s : N.State) (i : N.Inputs) :
  R.v22812 (state s) (inputs i) = Zmod.unsigned (N.v22812 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22812 s i)) at 1.
  unfold R.v22812, N.v22812.
  unfold R.v6, N.v6.
  rewrite !state_r701_nr_5F701.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r701_nr_5F701 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22813 (s : N.State) (i : N.Inputs) :
  R.v22813 (state s) (inputs i) = Zmod.unsigned (N.v22813 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22813 s i)) at 1.
  unfold R.v22813, N.v22813.
  unfold R.v6, N.v6.
  rewrite !state_r700_nr_5F700.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r700_nr_5F700 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22814 (s : N.State) (i : N.Inputs) :
  R.v22814 (state s) (inputs i) = Zmod.unsigned (N.v22814 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22814 s i)) at 1.
  unfold R.v22814, N.v22814.
  rewrite ?node_22812.
  rewrite ?node_22813.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22815 (s : N.State) (i : N.Inputs) :
  R.v22815 (state s) (inputs i) = Zmod.unsigned (N.v22815 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22815 s i)) at 1.
  unfold R.v22815, N.v22815.
  unfold R.v16484, N.v16484.
  rewrite ?node_22814.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22816 (s : N.State) (i : N.Inputs) :
  R.v22816 (state s) (inputs i) = Zmod.unsigned (N.v22816 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22816 s i)) at 1.
  unfold R.v22816, N.v22816.
  rewrite ?node_22811.
  rewrite ?node_22815.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22817 (s : N.State) (i : N.Inputs) :
  R.v22817 (state s) (inputs i) = Zmod.unsigned (N.v22817 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22817 s i)) at 1.
  unfold R.v22817, N.v22817.
  unfold R.v6, N.v6.
  rewrite ?node_22816.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22818 (s : N.State) (i : N.Inputs) :
  R.v22818 (state s) (inputs i) = Zmod.unsigned (N.v22818 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22818 s i)) at 1.
  unfold R.v22818, N.v22818.
  rewrite ?node_8296.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22819 (s : N.State) (i : N.Inputs) :
  R.v22819 (state s) (inputs i) = Zmod.unsigned (N.v22819 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22819 s i)) at 1.
  unfold R.v22819, N.v22819.
  unfold R.v6, N.v6.
  rewrite ?node_8425.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22820 (s : N.State) (i : N.Inputs) :
  R.v22820 (state s) (inputs i) = Zmod.unsigned (N.v22820 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22820 s i)) at 1.
  unfold R.v22820, N.v22820.
  rewrite ?node_22818.
  rewrite ?node_22819.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22821 (s : N.State) (i : N.Inputs) :
  R.v22821 (state s) (inputs i) = Zmod.unsigned (N.v22821 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22821 s i)) at 1.
  unfold R.v22821, N.v22821.
  rewrite ?node_22817.
  rewrite ?node_22820.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22822 (s : N.State) (i : N.Inputs) :
  R.v22822 (state s) (inputs i) = Zmod.unsigned (N.v22822 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22822 s i)) at 1.
  unfold R.v22822, N.v22822.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22823 (s : N.State) (i : N.Inputs) :
  R.v22823 (state s) (inputs i) = Zmod.unsigned (N.v22823 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22823 s i)) at 1.
  unfold R.v22823, N.v22823.
  rewrite ?node_8300.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22824 (s : N.State) (i : N.Inputs) :
  R.v22824 (state s) (inputs i) = Zmod.unsigned (N.v22824 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22824 s i)) at 1.
  unfold R.v22824, N.v22824.
  unfold R.v6, N.v6.
  rewrite !state_r703_nr_5F703.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r703_nr_5F703 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22825 (s : N.State) (i : N.Inputs) :
  R.v22825 (state s) (inputs i) = Zmod.unsigned (N.v22825 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22825 s i)) at 1.
  unfold R.v22825, N.v22825.
  unfold R.v6, N.v6.
  rewrite ?node_8296.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22826 (s : N.State) (i : N.Inputs) :
  R.v22826 (state s) (inputs i) = Zmod.unsigned (N.v22826 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22826 s i)) at 1.
  unfold R.v22826, N.v22826.
  rewrite ?node_22824.
  rewrite ?node_22825.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22827 (s : N.State) (i : N.Inputs) :
  R.v22827 (state s) (inputs i) = Zmod.unsigned (N.v22827 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22827 s i)) at 1.
  unfold R.v22827, N.v22827.
  unfold R.v16484, N.v16484.
  rewrite ?node_22826.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22828 (s : N.State) (i : N.Inputs) :
  R.v22828 (state s) (inputs i) = Zmod.unsigned (N.v22828 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22828 s i)) at 1.
  unfold R.v22828, N.v22828.
  rewrite ?node_22823.
  rewrite ?node_22827.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22829 (s : N.State) (i : N.Inputs) :
  R.v22829 (state s) (inputs i) = Zmod.unsigned (N.v22829 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22829 s i)) at 1.
  unfold R.v22829, N.v22829.
  unfold R.v6, N.v6.
  rewrite ?node_22828.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22830 (s : N.State) (i : N.Inputs) :
  R.v22830 (state s) (inputs i) = Zmod.unsigned (N.v22830 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22830 s i)) at 1.
  unfold R.v22830, N.v22830.
  rewrite ?node_8301.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22831 (s : N.State) (i : N.Inputs) :
  R.v22831 (state s) (inputs i) = Zmod.unsigned (N.v22831 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22831 s i)) at 1.
  unfold R.v22831, N.v22831.
  unfold R.v6, N.v6.
  rewrite ?node_8475.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22832 (s : N.State) (i : N.Inputs) :
  R.v22832 (state s) (inputs i) = Zmod.unsigned (N.v22832 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22832 s i)) at 1.
  unfold R.v22832, N.v22832.
  rewrite ?node_22830.
  rewrite ?node_22831.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22833 (s : N.State) (i : N.Inputs) :
  R.v22833 (state s) (inputs i) = Zmod.unsigned (N.v22833 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22833 s i)) at 1.
  unfold R.v22833, N.v22833.
  rewrite ?node_22829.
  rewrite ?node_22832.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22834 (s : N.State) (i : N.Inputs) :
  R.v22834 (state s) (inputs i) = Zmod.unsigned (N.v22834 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22834 s i)) at 1.
  unfold R.v22834, N.v22834.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22835 (s : N.State) (i : N.Inputs) :
  R.v22835 (state s) (inputs i) = Zmod.unsigned (N.v22835 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22835 s i)) at 1.
  unfold R.v22835, N.v22835.
  rewrite ?node_8307.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22836 (s : N.State) (i : N.Inputs) :
  R.v22836 (state s) (inputs i) = Zmod.unsigned (N.v22836 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22836 s i)) at 1.
  unfold R.v22836, N.v22836.
  unfold R.v16463, N.v16463.
  rewrite !state_r707_nr_5F707.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r707_nr_5F707 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22837 (s : N.State) (i : N.Inputs) :
  R.v22837 (state s) (inputs i) = Zmod.unsigned (N.v22837 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22837 s i)) at 1.
  unfold R.v22837, N.v22837.
  unfold R.v16463, N.v16463.
  rewrite !state_r706_nr_5F706.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r706_nr_5F706 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22838 (s : N.State) (i : N.Inputs) :
  R.v22838 (state s) (inputs i) = Zmod.unsigned (N.v22838 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22838 s i)) at 1.
  unfold R.v22838, N.v22838.
  unfold R.v6, N.v6.
  rewrite !state_r705_nr_5F705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r705_nr_5F705 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22839 (s : N.State) (i : N.Inputs) :
  R.v22839 (state s) (inputs i) = Zmod.unsigned (N.v22839 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22839 s i)) at 1.
  unfold R.v22839, N.v22839.
  unfold R.v6, N.v6.
  rewrite !state_r704_nr_5F704.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r704_nr_5F704 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22840 (s : N.State) (i : N.Inputs) :
  R.v22840 (state s) (inputs i) = Zmod.unsigned (N.v22840 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22840 s i)) at 1.
  unfold R.v22840, N.v22840.
  rewrite ?node_22838.
  rewrite ?node_22839.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22841 (s : N.State) (i : N.Inputs) :
  R.v22841 (state s) (inputs i) = Zmod.unsigned (N.v22841 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22841 s i)) at 1.
  unfold R.v22841, N.v22841.
  unfold R.v16484, N.v16484.
  rewrite ?node_22840.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22842 (s : N.State) (i : N.Inputs) :
  R.v22842 (state s) (inputs i) = Zmod.unsigned (N.v22842 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22842 s i)) at 1.
  unfold R.v22842, N.v22842.
  rewrite ?node_22835.
  rewrite ?node_22836.
  rewrite ?node_22837.
  rewrite ?node_22841.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22843 (s : N.State) (i : N.Inputs) :
  R.v22843 (state s) (inputs i) = Zmod.unsigned (N.v22843 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22843 s i)) at 1.
  unfold R.v22843, N.v22843.
  unfold R.v6, N.v6.
  rewrite ?node_22842.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22844 (s : N.State) (i : N.Inputs) :
  R.v22844 (state s) (inputs i) = Zmod.unsigned (N.v22844 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22844 s i)) at 1.
  unfold R.v22844, N.v22844.
  rewrite ?node_8308.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22845 (s : N.State) (i : N.Inputs) :
  R.v22845 (state s) (inputs i) = Zmod.unsigned (N.v22845 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22845 s i)) at 1.
  unfold R.v22845, N.v22845.
  unfold R.v6, N.v6.
  rewrite ?node_8432.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22846 (s : N.State) (i : N.Inputs) :
  R.v22846 (state s) (inputs i) = Zmod.unsigned (N.v22846 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22846 s i)) at 1.
  unfold R.v22846, N.v22846.
  unfold R.v6, N.v6.
  rewrite ?node_8484.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22847 (s : N.State) (i : N.Inputs) :
  R.v22847 (state s) (inputs i) = Zmod.unsigned (N.v22847 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22847 s i)) at 1.
  unfold R.v22847, N.v22847.
  rewrite ?node_22844.
  rewrite ?node_22845.
  rewrite ?node_22846.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22848 (s : N.State) (i : N.Inputs) :
  R.v22848 (state s) (inputs i) = Zmod.unsigned (N.v22848 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22848 s i)) at 1.
  unfold R.v22848, N.v22848.
  rewrite ?node_22843.
  rewrite ?node_22847.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22849 (s : N.State) (i : N.Inputs) :
  R.v22849 (state s) (inputs i) = Zmod.unsigned (N.v22849 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22849 s i)) at 1.
  unfold R.v22849, N.v22849.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22850 (s : N.State) (i : N.Inputs) :
  R.v22850 (state s) (inputs i) = Zmod.unsigned (N.v22850 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22850 s i)) at 1.
  unfold R.v22850, N.v22850.
  unfold R.v16463, N.v16463.
  rewrite !state_r706_nr_5F706.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r706_nr_5F706 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22851 (s : N.State) (i : N.Inputs) :
  R.v22851 (state s) (inputs i) = Zmod.unsigned (N.v22851 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22851 s i)) at 1.
  unfold R.v22851, N.v22851.
  unfold R.v6, N.v6.
  rewrite !state_r705_nr_5F705.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r705_nr_5F705 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22852 (s : N.State) (i : N.Inputs) :
  R.v22852 (state s) (inputs i) = Zmod.unsigned (N.v22852 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22852 s i)) at 1.
  unfold R.v22852, N.v22852.
  unfold R.v6, N.v6.
  rewrite !state_r704_nr_5F704.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r704_nr_5F704 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22853 (s : N.State) (i : N.Inputs) :
  R.v22853 (state s) (inputs i) = Zmod.unsigned (N.v22853 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22853 s i)) at 1.
  unfold R.v22853, N.v22853.
  rewrite ?node_22851.
  rewrite ?node_22852.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22854 (s : N.State) (i : N.Inputs) :
  R.v22854 (state s) (inputs i) = Zmod.unsigned (N.v22854 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22854 s i)) at 1.
  unfold R.v22854, N.v22854.
  unfold R.v16484, N.v16484.
  rewrite ?node_22853.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22855 (s : N.State) (i : N.Inputs) :
  R.v22855 (state s) (inputs i) = Zmod.unsigned (N.v22855 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22855 s i)) at 1.
  unfold R.v22855, N.v22855.
  rewrite ?node_22850.
  rewrite ?node_22854.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22856 (s : N.State) (i : N.Inputs) :
  R.v22856 (state s) (inputs i) = Zmod.unsigned (N.v22856 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22856 s i)) at 1.
  unfold R.v22856, N.v22856.
  unfold R.v6, N.v6.
  rewrite ?node_22855.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22857 (s : N.State) (i : N.Inputs) :
  R.v22857 (state s) (inputs i) = Zmod.unsigned (N.v22857 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22857 s i)) at 1.
  unfold R.v22857, N.v22857.
  rewrite ?node_8303.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22858 (s : N.State) (i : N.Inputs) :
  R.v22858 (state s) (inputs i) = Zmod.unsigned (N.v22858 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22858 s i)) at 1.
  unfold R.v22858, N.v22858.
  unfold R.v6, N.v6.
  rewrite ?node_8432.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22859 (s : N.State) (i : N.Inputs) :
  R.v22859 (state s) (inputs i) = Zmod.unsigned (N.v22859 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22859 s i)) at 1.
  unfold R.v22859, N.v22859.
  rewrite ?node_22857.
  rewrite ?node_22858.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22860 (s : N.State) (i : N.Inputs) :
  R.v22860 (state s) (inputs i) = Zmod.unsigned (N.v22860 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22860 s i)) at 1.
  unfold R.v22860, N.v22860.
  rewrite ?node_22856.
  rewrite ?node_22859.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22861 (s : N.State) (i : N.Inputs) :
  R.v22861 (state s) (inputs i) = Zmod.unsigned (N.v22861 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22861 s i)) at 1.
  unfold R.v22861, N.v22861.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22862 (s : N.State) (i : N.Inputs) :
  R.v22862 (state s) (inputs i) = Zmod.unsigned (N.v22862 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22862 s i)) at 1.
  unfold R.v22862, N.v22862.
  rewrite ?node_8307.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22863 (s : N.State) (i : N.Inputs) :
  R.v22863 (state s) (inputs i) = Zmod.unsigned (N.v22863 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22863 s i)) at 1.
  unfold R.v22863, N.v22863.
  unfold R.v6, N.v6.
  rewrite !state_r707_nr_5F707.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r707_nr_5F707 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22864 (s : N.State) (i : N.Inputs) :
  R.v22864 (state s) (inputs i) = Zmod.unsigned (N.v22864 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22864 s i)) at 1.
  unfold R.v22864, N.v22864.
  unfold R.v6, N.v6.
  rewrite ?node_8303.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22865 (s : N.State) (i : N.Inputs) :
  R.v22865 (state s) (inputs i) = Zmod.unsigned (N.v22865 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22865 s i)) at 1.
  unfold R.v22865, N.v22865.
  rewrite ?node_22863.
  rewrite ?node_22864.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22866 (s : N.State) (i : N.Inputs) :
  R.v22866 (state s) (inputs i) = Zmod.unsigned (N.v22866 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22866 s i)) at 1.
  unfold R.v22866, N.v22866.
  unfold R.v16484, N.v16484.
  rewrite ?node_22865.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22867 (s : N.State) (i : N.Inputs) :
  R.v22867 (state s) (inputs i) = Zmod.unsigned (N.v22867 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22867 s i)) at 1.
  unfold R.v22867, N.v22867.
  rewrite ?node_22862.
  rewrite ?node_22866.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22868 (s : N.State) (i : N.Inputs) :
  R.v22868 (state s) (inputs i) = Zmod.unsigned (N.v22868 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22868 s i)) at 1.
  unfold R.v22868, N.v22868.
  unfold R.v6, N.v6.
  rewrite ?node_22867.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22869 (s : N.State) (i : N.Inputs) :
  R.v22869 (state s) (inputs i) = Zmod.unsigned (N.v22869 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22869 s i)) at 1.
  unfold R.v22869, N.v22869.
  rewrite ?node_8308.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22870 (s : N.State) (i : N.Inputs) :
  R.v22870 (state s) (inputs i) = Zmod.unsigned (N.v22870 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22870 s i)) at 1.
  unfold R.v22870, N.v22870.
  unfold R.v6, N.v6.
  rewrite ?node_8484.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22871 (s : N.State) (i : N.Inputs) :
  R.v22871 (state s) (inputs i) = Zmod.unsigned (N.v22871 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22871 s i)) at 1.
  unfold R.v22871, N.v22871.
  rewrite ?node_22869.
  rewrite ?node_22870.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22872 (s : N.State) (i : N.Inputs) :
  R.v22872 (state s) (inputs i) = Zmod.unsigned (N.v22872 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22872 s i)) at 1.
  unfold R.v22872, N.v22872.
  rewrite ?node_22868.
  rewrite ?node_22871.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22873 (s : N.State) (i : N.Inputs) :
  R.v22873 (state s) (inputs i) = Zmod.unsigned (N.v22873 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22873 s i)) at 1.
  unfold R.v22873, N.v22873.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22874 (s : N.State) (i : N.Inputs) :
  R.v22874 (state s) (inputs i) = Zmod.unsigned (N.v22874 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22874 s i)) at 1.
  unfold R.v22874, N.v22874.
  rewrite ?node_8315.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22875 (s : N.State) (i : N.Inputs) :
  R.v22875 (state s) (inputs i) = Zmod.unsigned (N.v22875 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22875 s i)) at 1.
  unfold R.v22875, N.v22875.
  unfold R.v16463, N.v16463.
  rewrite !state_r711_nr_5F711.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r711_nr_5F711 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22876 (s : N.State) (i : N.Inputs) :
  R.v22876 (state s) (inputs i) = Zmod.unsigned (N.v22876 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22876 s i)) at 1.
  unfold R.v22876, N.v22876.
  unfold R.v16463, N.v16463.
  rewrite !state_r710_nr_5F710.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r710_nr_5F710 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22877 (s : N.State) (i : N.Inputs) :
  R.v22877 (state s) (inputs i) = Zmod.unsigned (N.v22877 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22877 s i)) at 1.
  unfold R.v22877, N.v22877.
  unfold R.v6, N.v6.
  rewrite !state_r709_nr_5F709.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r709_nr_5F709 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22878 (s : N.State) (i : N.Inputs) :
  R.v22878 (state s) (inputs i) = Zmod.unsigned (N.v22878 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22878 s i)) at 1.
  unfold R.v22878, N.v22878.
  unfold R.v6, N.v6.
  rewrite !state_r708_nr_5F708.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r708_nr_5F708 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22879 (s : N.State) (i : N.Inputs) :
  R.v22879 (state s) (inputs i) = Zmod.unsigned (N.v22879 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22879 s i)) at 1.
  unfold R.v22879, N.v22879.
  rewrite ?node_22877.
  rewrite ?node_22878.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22880 (s : N.State) (i : N.Inputs) :
  R.v22880 (state s) (inputs i) = Zmod.unsigned (N.v22880 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22880 s i)) at 1.
  unfold R.v22880, N.v22880.
  unfold R.v16484, N.v16484.
  rewrite ?node_22879.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22881 (s : N.State) (i : N.Inputs) :
  R.v22881 (state s) (inputs i) = Zmod.unsigned (N.v22881 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22881 s i)) at 1.
  unfold R.v22881, N.v22881.
  rewrite ?node_22874.
  rewrite ?node_22875.
  rewrite ?node_22876.
  rewrite ?node_22880.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22882 (s : N.State) (i : N.Inputs) :
  R.v22882 (state s) (inputs i) = Zmod.unsigned (N.v22882 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22882 s i)) at 1.
  unfold R.v22882, N.v22882.
  unfold R.v6, N.v6.
  rewrite ?node_22881.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22883 (s : N.State) (i : N.Inputs) :
  R.v22883 (state s) (inputs i) = Zmod.unsigned (N.v22883 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22883 s i)) at 1.
  unfold R.v22883, N.v22883.
  rewrite ?node_8316.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22884 (s : N.State) (i : N.Inputs) :
  R.v22884 (state s) (inputs i) = Zmod.unsigned (N.v22884 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22884 s i)) at 1.
  unfold R.v22884, N.v22884.
  unfold R.v6, N.v6.
  rewrite ?node_8440.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22885 (s : N.State) (i : N.Inputs) :
  R.v22885 (state s) (inputs i) = Zmod.unsigned (N.v22885 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22885 s i)) at 1.
  unfold R.v22885, N.v22885.
  unfold R.v6, N.v6.
  rewrite ?node_8487.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22886 (s : N.State) (i : N.Inputs) :
  R.v22886 (state s) (inputs i) = Zmod.unsigned (N.v22886 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22886 s i)) at 1.
  unfold R.v22886, N.v22886.
  rewrite ?node_22883.
  rewrite ?node_22884.
  rewrite ?node_22885.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22887 (s : N.State) (i : N.Inputs) :
  R.v22887 (state s) (inputs i) = Zmod.unsigned (N.v22887 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22887 s i)) at 1.
  unfold R.v22887, N.v22887.
  rewrite ?node_22882.
  rewrite ?node_22886.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22888 (s : N.State) (i : N.Inputs) :
  R.v22888 (state s) (inputs i) = Zmod.unsigned (N.v22888 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22888 s i)) at 1.
  unfold R.v22888, N.v22888.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22889 (s : N.State) (i : N.Inputs) :
  R.v22889 (state s) (inputs i) = Zmod.unsigned (N.v22889 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22889 s i)) at 1.
  unfold R.v22889, N.v22889.
  unfold R.v16463, N.v16463.
  rewrite !state_r710_nr_5F710.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r710_nr_5F710 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22890 (s : N.State) (i : N.Inputs) :
  R.v22890 (state s) (inputs i) = Zmod.unsigned (N.v22890 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22890 s i)) at 1.
  unfold R.v22890, N.v22890.
  unfold R.v6, N.v6.
  rewrite !state_r709_nr_5F709.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r709_nr_5F709 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22891 (s : N.State) (i : N.Inputs) :
  R.v22891 (state s) (inputs i) = Zmod.unsigned (N.v22891 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22891 s i)) at 1.
  unfold R.v22891, N.v22891.
  unfold R.v6, N.v6.
  rewrite !state_r708_nr_5F708.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r708_nr_5F708 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22892 (s : N.State) (i : N.Inputs) :
  R.v22892 (state s) (inputs i) = Zmod.unsigned (N.v22892 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22892 s i)) at 1.
  unfold R.v22892, N.v22892.
  rewrite ?node_22890.
  rewrite ?node_22891.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22893 (s : N.State) (i : N.Inputs) :
  R.v22893 (state s) (inputs i) = Zmod.unsigned (N.v22893 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22893 s i)) at 1.
  unfold R.v22893, N.v22893.
  unfold R.v16484, N.v16484.
  rewrite ?node_22892.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22894 (s : N.State) (i : N.Inputs) :
  R.v22894 (state s) (inputs i) = Zmod.unsigned (N.v22894 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22894 s i)) at 1.
  unfold R.v22894, N.v22894.
  rewrite ?node_22889.
  rewrite ?node_22893.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22895 (s : N.State) (i : N.Inputs) :
  R.v22895 (state s) (inputs i) = Zmod.unsigned (N.v22895 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22895 s i)) at 1.
  unfold R.v22895, N.v22895.
  unfold R.v6, N.v6.
  rewrite ?node_22894.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22896 (s : N.State) (i : N.Inputs) :
  R.v22896 (state s) (inputs i) = Zmod.unsigned (N.v22896 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22896 s i)) at 1.
  unfold R.v22896, N.v22896.
  rewrite ?node_8311.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22897 (s : N.State) (i : N.Inputs) :
  R.v22897 (state s) (inputs i) = Zmod.unsigned (N.v22897 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22897 s i)) at 1.
  unfold R.v22897, N.v22897.
  unfold R.v6, N.v6.
  rewrite ?node_8440.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22898 (s : N.State) (i : N.Inputs) :
  R.v22898 (state s) (inputs i) = Zmod.unsigned (N.v22898 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22898 s i)) at 1.
  unfold R.v22898, N.v22898.
  rewrite ?node_22896.
  rewrite ?node_22897.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22899 (s : N.State) (i : N.Inputs) :
  R.v22899 (state s) (inputs i) = Zmod.unsigned (N.v22899 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22899 s i)) at 1.
  unfold R.v22899, N.v22899.
  rewrite ?node_22895.
  rewrite ?node_22898.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22900 (s : N.State) (i : N.Inputs) :
  R.v22900 (state s) (inputs i) = Zmod.unsigned (N.v22900 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22900 s i)) at 1.
  unfold R.v22900, N.v22900.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22901 (s : N.State) (i : N.Inputs) :
  R.v22901 (state s) (inputs i) = Zmod.unsigned (N.v22901 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22901 s i)) at 1.
  unfold R.v22901, N.v22901.
  rewrite ?node_8315.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22902 (s : N.State) (i : N.Inputs) :
  R.v22902 (state s) (inputs i) = Zmod.unsigned (N.v22902 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22902 s i)) at 1.
  unfold R.v22902, N.v22902.
  unfold R.v6, N.v6.
  rewrite !state_r711_nr_5F711.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r711_nr_5F711 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22903 (s : N.State) (i : N.Inputs) :
  R.v22903 (state s) (inputs i) = Zmod.unsigned (N.v22903 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22903 s i)) at 1.
  unfold R.v22903, N.v22903.
  unfold R.v6, N.v6.
  rewrite ?node_8311.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22904 (s : N.State) (i : N.Inputs) :
  R.v22904 (state s) (inputs i) = Zmod.unsigned (N.v22904 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22904 s i)) at 1.
  unfold R.v22904, N.v22904.
  rewrite ?node_22902.
  rewrite ?node_22903.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22905 (s : N.State) (i : N.Inputs) :
  R.v22905 (state s) (inputs i) = Zmod.unsigned (N.v22905 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22905 s i)) at 1.
  unfold R.v22905, N.v22905.
  unfold R.v16484, N.v16484.
  rewrite ?node_22904.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22906 (s : N.State) (i : N.Inputs) :
  R.v22906 (state s) (inputs i) = Zmod.unsigned (N.v22906 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22906 s i)) at 1.
  unfold R.v22906, N.v22906.
  rewrite ?node_22901.
  rewrite ?node_22905.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22907 (s : N.State) (i : N.Inputs) :
  R.v22907 (state s) (inputs i) = Zmod.unsigned (N.v22907 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22907 s i)) at 1.
  unfold R.v22907, N.v22907.
  unfold R.v6, N.v6.
  rewrite ?node_22906.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22908 (s : N.State) (i : N.Inputs) :
  R.v22908 (state s) (inputs i) = Zmod.unsigned (N.v22908 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22908 s i)) at 1.
  unfold R.v22908, N.v22908.
  rewrite ?node_8316.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22909 (s : N.State) (i : N.Inputs) :
  R.v22909 (state s) (inputs i) = Zmod.unsigned (N.v22909 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22909 s i)) at 1.
  unfold R.v22909, N.v22909.
  unfold R.v6, N.v6.
  rewrite ?node_8487.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22910 (s : N.State) (i : N.Inputs) :
  R.v22910 (state s) (inputs i) = Zmod.unsigned (N.v22910 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22910 s i)) at 1.
  unfold R.v22910, N.v22910.
  rewrite ?node_22908.
  rewrite ?node_22909.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22911 (s : N.State) (i : N.Inputs) :
  R.v22911 (state s) (inputs i) = Zmod.unsigned (N.v22911 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22911 s i)) at 1.
  unfold R.v22911, N.v22911.
  rewrite ?node_22907.
  rewrite ?node_22910.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22912 (s : N.State) (i : N.Inputs) :
  R.v22912 (state s) (inputs i) = Zmod.unsigned (N.v22912 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22912 s i)) at 1.
  unfold R.v22912, N.v22912.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22913 (s : N.State) (i : N.Inputs) :
  R.v22913 (state s) (inputs i) = Zmod.unsigned (N.v22913 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22913 s i)) at 1.
  unfold R.v22913, N.v22913.
  rewrite ?node_8323.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22914 (s : N.State) (i : N.Inputs) :
  R.v22914 (state s) (inputs i) = Zmod.unsigned (N.v22914 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22914 s i)) at 1.
  unfold R.v22914, N.v22914.
  unfold R.v16463, N.v16463.
  rewrite !state_r715_nr_5F715.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r715_nr_5F715 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22915 (s : N.State) (i : N.Inputs) :
  R.v22915 (state s) (inputs i) = Zmod.unsigned (N.v22915 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22915 s i)) at 1.
  unfold R.v22915, N.v22915.
  unfold R.v16463, N.v16463.
  rewrite !state_r714_nr_5F714.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r714_nr_5F714 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22916 (s : N.State) (i : N.Inputs) :
  R.v22916 (state s) (inputs i) = Zmod.unsigned (N.v22916 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22916 s i)) at 1.
  unfold R.v22916, N.v22916.
  unfold R.v6, N.v6.
  rewrite !state_r713_nr_5F713.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r713_nr_5F713 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22917 (s : N.State) (i : N.Inputs) :
  R.v22917 (state s) (inputs i) = Zmod.unsigned (N.v22917 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22917 s i)) at 1.
  unfold R.v22917, N.v22917.
  unfold R.v6, N.v6.
  rewrite !state_r712_nr_5F712.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r712_nr_5F712 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22918 (s : N.State) (i : N.Inputs) :
  R.v22918 (state s) (inputs i) = Zmod.unsigned (N.v22918 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22918 s i)) at 1.
  unfold R.v22918, N.v22918.
  rewrite ?node_22916.
  rewrite ?node_22917.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22919 (s : N.State) (i : N.Inputs) :
  R.v22919 (state s) (inputs i) = Zmod.unsigned (N.v22919 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22919 s i)) at 1.
  unfold R.v22919, N.v22919.
  unfold R.v16484, N.v16484.
  rewrite ?node_22918.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22920 (s : N.State) (i : N.Inputs) :
  R.v22920 (state s) (inputs i) = Zmod.unsigned (N.v22920 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22920 s i)) at 1.
  unfold R.v22920, N.v22920.
  rewrite ?node_22913.
  rewrite ?node_22914.
  rewrite ?node_22915.
  rewrite ?node_22919.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22921 (s : N.State) (i : N.Inputs) :
  R.v22921 (state s) (inputs i) = Zmod.unsigned (N.v22921 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22921 s i)) at 1.
  unfold R.v22921, N.v22921.
  unfold R.v6, N.v6.
  rewrite ?node_22920.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22922 (s : N.State) (i : N.Inputs) :
  R.v22922 (state s) (inputs i) = Zmod.unsigned (N.v22922 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22922 s i)) at 1.
  unfold R.v22922, N.v22922.
  rewrite ?node_8324.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22923 (s : N.State) (i : N.Inputs) :
  R.v22923 (state s) (inputs i) = Zmod.unsigned (N.v22923 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22923 s i)) at 1.
  unfold R.v22923, N.v22923.
  unfold R.v6, N.v6.
  rewrite ?node_8448.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22924 (s : N.State) (i : N.Inputs) :
  R.v22924 (state s) (inputs i) = Zmod.unsigned (N.v22924 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22924 s i)) at 1.
  unfold R.v22924, N.v22924.
  unfold R.v6, N.v6.
  rewrite ?node_8491.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22925 (s : N.State) (i : N.Inputs) :
  R.v22925 (state s) (inputs i) = Zmod.unsigned (N.v22925 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22925 s i)) at 1.
  unfold R.v22925, N.v22925.
  rewrite ?node_22922.
  rewrite ?node_22923.
  rewrite ?node_22924.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22926 (s : N.State) (i : N.Inputs) :
  R.v22926 (state s) (inputs i) = Zmod.unsigned (N.v22926 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22926 s i)) at 1.
  unfold R.v22926, N.v22926.
  rewrite ?node_22921.
  rewrite ?node_22925.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22927 (s : N.State) (i : N.Inputs) :
  R.v22927 (state s) (inputs i) = Zmod.unsigned (N.v22927 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22927 s i)) at 1.
  unfold R.v22927, N.v22927.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22928 (s : N.State) (i : N.Inputs) :
  R.v22928 (state s) (inputs i) = Zmod.unsigned (N.v22928 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22928 s i)) at 1.
  unfold R.v22928, N.v22928.
  unfold R.v16463, N.v16463.
  rewrite !state_r714_nr_5F714.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r714_nr_5F714 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22929 (s : N.State) (i : N.Inputs) :
  R.v22929 (state s) (inputs i) = Zmod.unsigned (N.v22929 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22929 s i)) at 1.
  unfold R.v22929, N.v22929.
  unfold R.v6, N.v6.
  rewrite !state_r713_nr_5F713.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r713_nr_5F713 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22930 (s : N.State) (i : N.Inputs) :
  R.v22930 (state s) (inputs i) = Zmod.unsigned (N.v22930 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22930 s i)) at 1.
  unfold R.v22930, N.v22930.
  unfold R.v6, N.v6.
  rewrite !state_r712_nr_5F712.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r712_nr_5F712 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22931 (s : N.State) (i : N.Inputs) :
  R.v22931 (state s) (inputs i) = Zmod.unsigned (N.v22931 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22931 s i)) at 1.
  unfold R.v22931, N.v22931.
  rewrite ?node_22929.
  rewrite ?node_22930.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22932 (s : N.State) (i : N.Inputs) :
  R.v22932 (state s) (inputs i) = Zmod.unsigned (N.v22932 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22932 s i)) at 1.
  unfold R.v22932, N.v22932.
  unfold R.v16484, N.v16484.
  rewrite ?node_22931.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22933 (s : N.State) (i : N.Inputs) :
  R.v22933 (state s) (inputs i) = Zmod.unsigned (N.v22933 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22933 s i)) at 1.
  unfold R.v22933, N.v22933.
  rewrite ?node_22928.
  rewrite ?node_22932.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22934 (s : N.State) (i : N.Inputs) :
  R.v22934 (state s) (inputs i) = Zmod.unsigned (N.v22934 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22934 s i)) at 1.
  unfold R.v22934, N.v22934.
  unfold R.v6, N.v6.
  rewrite ?node_22933.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22935 (s : N.State) (i : N.Inputs) :
  R.v22935 (state s) (inputs i) = Zmod.unsigned (N.v22935 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22935 s i)) at 1.
  unfold R.v22935, N.v22935.
  rewrite ?node_8319.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22936 (s : N.State) (i : N.Inputs) :
  R.v22936 (state s) (inputs i) = Zmod.unsigned (N.v22936 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22936 s i)) at 1.
  unfold R.v22936, N.v22936.
  unfold R.v6, N.v6.
  rewrite ?node_8448.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22937 (s : N.State) (i : N.Inputs) :
  R.v22937 (state s) (inputs i) = Zmod.unsigned (N.v22937 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22937 s i)) at 1.
  unfold R.v22937, N.v22937.
  rewrite ?node_22935.
  rewrite ?node_22936.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22938 (s : N.State) (i : N.Inputs) :
  R.v22938 (state s) (inputs i) = Zmod.unsigned (N.v22938 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22938 s i)) at 1.
  unfold R.v22938, N.v22938.
  rewrite ?node_22934.
  rewrite ?node_22937.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22939 (s : N.State) (i : N.Inputs) :
  R.v22939 (state s) (inputs i) = Zmod.unsigned (N.v22939 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22939 s i)) at 1.
  unfold R.v22939, N.v22939.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22940 (s : N.State) (i : N.Inputs) :
  R.v22940 (state s) (inputs i) = Zmod.unsigned (N.v22940 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22940 s i)) at 1.
  unfold R.v22940, N.v22940.
  rewrite ?node_8323.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22941 (s : N.State) (i : N.Inputs) :
  R.v22941 (state s) (inputs i) = Zmod.unsigned (N.v22941 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22941 s i)) at 1.
  unfold R.v22941, N.v22941.
  unfold R.v6, N.v6.
  rewrite !state_r715_nr_5F715.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r715_nr_5F715 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22942 (s : N.State) (i : N.Inputs) :
  R.v22942 (state s) (inputs i) = Zmod.unsigned (N.v22942 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22942 s i)) at 1.
  unfold R.v22942, N.v22942.
  unfold R.v6, N.v6.
  rewrite ?node_8319.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22943 (s : N.State) (i : N.Inputs) :
  R.v22943 (state s) (inputs i) = Zmod.unsigned (N.v22943 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22943 s i)) at 1.
  unfold R.v22943, N.v22943.
  rewrite ?node_22941.
  rewrite ?node_22942.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22944 (s : N.State) (i : N.Inputs) :
  R.v22944 (state s) (inputs i) = Zmod.unsigned (N.v22944 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22944 s i)) at 1.
  unfold R.v22944, N.v22944.
  unfold R.v16484, N.v16484.
  rewrite ?node_22943.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22945 (s : N.State) (i : N.Inputs) :
  R.v22945 (state s) (inputs i) = Zmod.unsigned (N.v22945 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22945 s i)) at 1.
  unfold R.v22945, N.v22945.
  rewrite ?node_22940.
  rewrite ?node_22944.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22946 (s : N.State) (i : N.Inputs) :
  R.v22946 (state s) (inputs i) = Zmod.unsigned (N.v22946 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22946 s i)) at 1.
  unfold R.v22946, N.v22946.
  unfold R.v6, N.v6.
  rewrite ?node_22945.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22947 (s : N.State) (i : N.Inputs) :
  R.v22947 (state s) (inputs i) = Zmod.unsigned (N.v22947 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22947 s i)) at 1.
  unfold R.v22947, N.v22947.
  rewrite ?node_8324.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22948 (s : N.State) (i : N.Inputs) :
  R.v22948 (state s) (inputs i) = Zmod.unsigned (N.v22948 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22948 s i)) at 1.
  unfold R.v22948, N.v22948.
  unfold R.v6, N.v6.
  rewrite ?node_8491.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22949 (s : N.State) (i : N.Inputs) :
  R.v22949 (state s) (inputs i) = Zmod.unsigned (N.v22949 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22949 s i)) at 1.
  unfold R.v22949, N.v22949.
  rewrite ?node_22947.
  rewrite ?node_22948.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22950 (s : N.State) (i : N.Inputs) :
  R.v22950 (state s) (inputs i) = Zmod.unsigned (N.v22950 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22950 s i)) at 1.
  unfold R.v22950, N.v22950.
  rewrite ?node_22946.
  rewrite ?node_22949.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22951 (s : N.State) (i : N.Inputs) :
  R.v22951 (state s) (inputs i) = Zmod.unsigned (N.v22951 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22951 s i)) at 1.
  unfold R.v22951, N.v22951.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22952 (s : N.State) (i : N.Inputs) :
  R.v22952 (state s) (inputs i) = Zmod.unsigned (N.v22952 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22952 s i)) at 1.
  unfold R.v22952, N.v22952.
  rewrite ?node_8335.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22953 (s : N.State) (i : N.Inputs) :
  R.v22953 (state s) (inputs i) = Zmod.unsigned (N.v22953 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22953 s i)) at 1.
  unfold R.v22953, N.v22953.
  unfold R.v16463, N.v16463.
  rewrite !state_r719_nr_5F719.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r719_nr_5F719 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22954 (s : N.State) (i : N.Inputs) :
  R.v22954 (state s) (inputs i) = Zmod.unsigned (N.v22954 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22954 s i)) at 1.
  unfold R.v22954, N.v22954.
  unfold R.v16463, N.v16463.
  rewrite !state_r718_nr_5F718.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r718_nr_5F718 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22955 (s : N.State) (i : N.Inputs) :
  R.v22955 (state s) (inputs i) = Zmod.unsigned (N.v22955 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22955 s i)) at 1.
  unfold R.v22955, N.v22955.
  unfold R.v6, N.v6.
  rewrite !state_r717_nr_5F717.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r717_nr_5F717 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22956 (s : N.State) (i : N.Inputs) :
  R.v22956 (state s) (inputs i) = Zmod.unsigned (N.v22956 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22956 s i)) at 1.
  unfold R.v22956, N.v22956.
  unfold R.v6, N.v6.
  rewrite !state_r716_nr_5F716.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r716_nr_5F716 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22957 (s : N.State) (i : N.Inputs) :
  R.v22957 (state s) (inputs i) = Zmod.unsigned (N.v22957 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22957 s i)) at 1.
  unfold R.v22957, N.v22957.
  rewrite ?node_22955.
  rewrite ?node_22956.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22958 (s : N.State) (i : N.Inputs) :
  R.v22958 (state s) (inputs i) = Zmod.unsigned (N.v22958 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22958 s i)) at 1.
  unfold R.v22958, N.v22958.
  unfold R.v16484, N.v16484.
  rewrite ?node_22957.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22959 (s : N.State) (i : N.Inputs) :
  R.v22959 (state s) (inputs i) = Zmod.unsigned (N.v22959 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22959 s i)) at 1.
  unfold R.v22959, N.v22959.
  rewrite ?node_22952.
  rewrite ?node_22953.
  rewrite ?node_22954.
  rewrite ?node_22958.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22960 (s : N.State) (i : N.Inputs) :
  R.v22960 (state s) (inputs i) = Zmod.unsigned (N.v22960 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22960 s i)) at 1.
  unfold R.v22960, N.v22960.
  unfold R.v6, N.v6.
  rewrite ?node_22959.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22961 (s : N.State) (i : N.Inputs) :
  R.v22961 (state s) (inputs i) = Zmod.unsigned (N.v22961 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22961 s i)) at 1.
  unfold R.v22961, N.v22961.
  rewrite ?node_8336.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22962 (s : N.State) (i : N.Inputs) :
  R.v22962 (state s) (inputs i) = Zmod.unsigned (N.v22962 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22962 s i)) at 1.
  unfold R.v22962, N.v22962.
  unfold R.v6, N.v6.
  rewrite ?node_8460.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22963 (s : N.State) (i : N.Inputs) :
  R.v22963 (state s) (inputs i) = Zmod.unsigned (N.v22963 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22963 s i)) at 1.
  unfold R.v22963, N.v22963.
  unfold R.v6, N.v6.
  rewrite ?node_8495.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22964 (s : N.State) (i : N.Inputs) :
  R.v22964 (state s) (inputs i) = Zmod.unsigned (N.v22964 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22964 s i)) at 1.
  unfold R.v22964, N.v22964.
  rewrite ?node_22961.
  rewrite ?node_22962.
  rewrite ?node_22963.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22965 (s : N.State) (i : N.Inputs) :
  R.v22965 (state s) (inputs i) = Zmod.unsigned (N.v22965 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22965 s i)) at 1.
  unfold R.v22965, N.v22965.
  rewrite ?node_22960.
  rewrite ?node_22964.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22966 (s : N.State) (i : N.Inputs) :
  R.v22966 (state s) (inputs i) = Zmod.unsigned (N.v22966 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22966 s i)) at 1.
  unfold R.v22966, N.v22966.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22967 (s : N.State) (i : N.Inputs) :
  R.v22967 (state s) (inputs i) = Zmod.unsigned (N.v22967 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22967 s i)) at 1.
  unfold R.v22967, N.v22967.
  unfold R.v16463, N.v16463.
  rewrite !state_r718_nr_5F718.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r718_nr_5F718 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22968 (s : N.State) (i : N.Inputs) :
  R.v22968 (state s) (inputs i) = Zmod.unsigned (N.v22968 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22968 s i)) at 1.
  unfold R.v22968, N.v22968.
  unfold R.v6, N.v6.
  rewrite !state_r717_nr_5F717.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r717_nr_5F717 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22969 (s : N.State) (i : N.Inputs) :
  R.v22969 (state s) (inputs i) = Zmod.unsigned (N.v22969 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22969 s i)) at 1.
  unfold R.v22969, N.v22969.
  unfold R.v6, N.v6.
  rewrite !state_r716_nr_5F716.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r716_nr_5F716 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22970 (s : N.State) (i : N.Inputs) :
  R.v22970 (state s) (inputs i) = Zmod.unsigned (N.v22970 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22970 s i)) at 1.
  unfold R.v22970, N.v22970.
  rewrite ?node_22968.
  rewrite ?node_22969.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22971 (s : N.State) (i : N.Inputs) :
  R.v22971 (state s) (inputs i) = Zmod.unsigned (N.v22971 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22971 s i)) at 1.
  unfold R.v22971, N.v22971.
  unfold R.v16484, N.v16484.
  rewrite ?node_22970.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22972 (s : N.State) (i : N.Inputs) :
  R.v22972 (state s) (inputs i) = Zmod.unsigned (N.v22972 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22972 s i)) at 1.
  unfold R.v22972, N.v22972.
  rewrite ?node_22967.
  rewrite ?node_22971.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22973 (s : N.State) (i : N.Inputs) :
  R.v22973 (state s) (inputs i) = Zmod.unsigned (N.v22973 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22973 s i)) at 1.
  unfold R.v22973, N.v22973.
  unfold R.v6, N.v6.
  rewrite ?node_22972.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22974 (s : N.State) (i : N.Inputs) :
  R.v22974 (state s) (inputs i) = Zmod.unsigned (N.v22974 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22974 s i)) at 1.
  unfold R.v22974, N.v22974.
  rewrite ?node_8331.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22975 (s : N.State) (i : N.Inputs) :
  R.v22975 (state s) (inputs i) = Zmod.unsigned (N.v22975 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22975 s i)) at 1.
  unfold R.v22975, N.v22975.
  unfold R.v6, N.v6.
  rewrite ?node_8460.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22976 (s : N.State) (i : N.Inputs) :
  R.v22976 (state s) (inputs i) = Zmod.unsigned (N.v22976 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22976 s i)) at 1.
  unfold R.v22976, N.v22976.
  rewrite ?node_22974.
  rewrite ?node_22975.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22977 (s : N.State) (i : N.Inputs) :
  R.v22977 (state s) (inputs i) = Zmod.unsigned (N.v22977 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22977 s i)) at 1.
  unfold R.v22977, N.v22977.
  rewrite ?node_22973.
  rewrite ?node_22976.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22978 (s : N.State) (i : N.Inputs) :
  R.v22978 (state s) (inputs i) = Zmod.unsigned (N.v22978 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22978 s i)) at 1.
  unfold R.v22978, N.v22978.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22979 (s : N.State) (i : N.Inputs) :
  R.v22979 (state s) (inputs i) = Zmod.unsigned (N.v22979 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22979 s i)) at 1.
  unfold R.v22979, N.v22979.
  rewrite ?node_8335.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22980 (s : N.State) (i : N.Inputs) :
  R.v22980 (state s) (inputs i) = Zmod.unsigned (N.v22980 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22980 s i)) at 1.
  unfold R.v22980, N.v22980.
  unfold R.v6, N.v6.
  rewrite !state_r719_nr_5F719.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r719_nr_5F719 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22981 (s : N.State) (i : N.Inputs) :
  R.v22981 (state s) (inputs i) = Zmod.unsigned (N.v22981 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22981 s i)) at 1.
  unfold R.v22981, N.v22981.
  unfold R.v6, N.v6.
  rewrite ?node_8331.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22982 (s : N.State) (i : N.Inputs) :
  R.v22982 (state s) (inputs i) = Zmod.unsigned (N.v22982 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22982 s i)) at 1.
  unfold R.v22982, N.v22982.
  rewrite ?node_22980.
  rewrite ?node_22981.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22983 (s : N.State) (i : N.Inputs) :
  R.v22983 (state s) (inputs i) = Zmod.unsigned (N.v22983 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22983 s i)) at 1.
  unfold R.v22983, N.v22983.
  unfold R.v16484, N.v16484.
  rewrite ?node_22982.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22984 (s : N.State) (i : N.Inputs) :
  R.v22984 (state s) (inputs i) = Zmod.unsigned (N.v22984 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22984 s i)) at 1.
  unfold R.v22984, N.v22984.
  rewrite ?node_22979.
  rewrite ?node_22983.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22985 (s : N.State) (i : N.Inputs) :
  R.v22985 (state s) (inputs i) = Zmod.unsigned (N.v22985 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22985 s i)) at 1.
  unfold R.v22985, N.v22985.
  unfold R.v6, N.v6.
  rewrite ?node_22984.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22986 (s : N.State) (i : N.Inputs) :
  R.v22986 (state s) (inputs i) = Zmod.unsigned (N.v22986 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22986 s i)) at 1.
  unfold R.v22986, N.v22986.
  rewrite ?node_8336.
  unfold R.v16468, N.v16468.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22987 (s : N.State) (i : N.Inputs) :
  R.v22987 (state s) (inputs i) = Zmod.unsigned (N.v22987 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22987 s i)) at 1.
  unfold R.v22987, N.v22987.
  unfold R.v6, N.v6.
  rewrite ?node_8495.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22988 (s : N.State) (i : N.Inputs) :
  R.v22988 (state s) (inputs i) = Zmod.unsigned (N.v22988 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22988 s i)) at 1.
  unfold R.v22988, N.v22988.
  rewrite ?node_22986.
  rewrite ?node_22987.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22989 (s : N.State) (i : N.Inputs) :
  R.v22989 (state s) (inputs i) = Zmod.unsigned (N.v22989 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22989 s i)) at 1.
  unfold R.v22989, N.v22989.
  rewrite ?node_22985.
  rewrite ?node_22988.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22990 (s : N.State) (i : N.Inputs) :
  R.v22990 (state s) (inputs i) = Zmod.unsigned (N.v22990 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22990 s i)) at 1.
  unfold R.v22990, N.v22990.
  unfold R.v3021, N.v3021.
  rewrite !inputs_nreset.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.nreset i)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22991 (s : N.State) (i : N.Inputs) :
  R.v22991 (state s) (inputs i) = Zmod.unsigned (N.v22991 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22991 s i)) at 1.
  unfold R.v22991, N.v22991.
  rewrite ?node_8342.
  unfold R.v16463, N.v16463.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22992 (s : N.State) (i : N.Inputs) :
  R.v22992 (state s) (inputs i) = Zmod.unsigned (N.v22992 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22992 s i)) at 1.
  unfold R.v22992, N.v22992.
  unfold R.v16463, N.v16463.
  rewrite !state_r723_nr_5F723.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r723_nr_5F723 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22993 (s : N.State) (i : N.Inputs) :
  R.v22993 (state s) (inputs i) = Zmod.unsigned (N.v22993 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22993 s i)) at 1.
  unfold R.v22993, N.v22993.
  unfold R.v16463, N.v16463.
  rewrite !state_r722_nr_5F722.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r722_nr_5F722 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22994 (s : N.State) (i : N.Inputs) :
  R.v22994 (state s) (inputs i) = Zmod.unsigned (N.v22994 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22994 s i)) at 1.
  unfold R.v22994, N.v22994.
  unfold R.v6, N.v6.
  rewrite !state_r721_nr_5F721.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r721_nr_5F721 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22995 (s : N.State) (i : N.Inputs) :
  R.v22995 (state s) (inputs i) = Zmod.unsigned (N.v22995 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22995 s i)) at 1.
  unfold R.v22995, N.v22995.
  unfold R.v6, N.v6.
  rewrite !state_r720_nr_5F720.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  rewrite ?(bits.mod_to_Z (N.r720_nr_5F720 s)).
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22996 (s : N.State) (i : N.Inputs) :
  R.v22996 (state s) (inputs i) = Zmod.unsigned (N.v22996 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22996 s i)) at 1.
  unfold R.v22996, N.v22996.
  rewrite ?node_22994.
  rewrite ?node_22995.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22997 (s : N.State) (i : N.Inputs) :
  R.v22997 (state s) (inputs i) = Zmod.unsigned (N.v22997 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22997 s i)) at 1.
  unfold R.v22997, N.v22997.
  unfold R.v16484, N.v16484.
  rewrite ?node_22996.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22998 (s : N.State) (i : N.Inputs) :
  R.v22998 (state s) (inputs i) = Zmod.unsigned (N.v22998 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22998 s i)) at 1.
  unfold R.v22998, N.v22998.
  rewrite ?node_22991.
  rewrite ?node_22992.
  rewrite ?node_22993.
  rewrite ?node_22997.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.

Lemma node_22999 (s : N.State) (i : N.Inputs) :
  R.v22999 (state s) (inputs i) = Zmod.unsigned (N.v22999 s i).
Proof.
  rewrite <- (bits.mod_to_Z (N.v22999 s i)) at 1.
  unfold R.v22999, N.v22999.
  unfold R.v6, N.v6.
  rewrite ?node_22998.
  unfold ReferenceGenerated.ArrayMulDataModule.CIRCTBits.word.
  normalize_node;
  repeat first [progress rewrite <-Z.add_assoc | rewrite Z.add_mod_idemp_l by (apply Z.pow_nonzero; lia) |
    rewrite Z.add_mod_idemp_r by (apply Z.pow_nonzero; lia)];
  try reflexivity; try (f_equal; lia).
Qed.
